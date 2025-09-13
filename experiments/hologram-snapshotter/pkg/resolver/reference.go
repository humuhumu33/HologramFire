package resolver

import (
	"fmt"
	"strings"
)

// Reference represents a parsed Docker reference
type Reference struct {
	Host       string
	Repository string
	Tag        string
	Digest     string
}

// String returns the string representation of the reference
func (r *Reference) String() string {
	if r.Digest != "" {
		return fmt.Sprintf("%s/%s@%s", r.Host, r.Repository, r.Digest)
	}
	return fmt.Sprintf("%s/%s:%s", r.Host, r.Repository, r.Tag)
}

// parseReference parses a Docker reference string
func parseReference(ref string) (*Reference, error) {
	// Handle digest references (e.g., registry.com/repo@sha256:...)
	if strings.Contains(ref, "@") {
		parts := strings.SplitN(ref, "@", 2)
		if len(parts) != 2 {
			return nil, fmt.Errorf("invalid digest reference: %s", ref)
		}

		hostRepo := parts[0]
		digest := parts[1]

		host, repository, err := parseHostRepository(hostRepo)
		if err != nil {
			return nil, err
		}

		return &Reference{
			Host:       host,
			Repository: repository,
			Digest:     digest,
		}, nil
	}

	// Handle tag references (e.g., registry.com/repo:tag)
	if strings.Contains(ref, ":") {
		parts := strings.SplitN(ref, ":", 2)
		if len(parts) != 2 {
			return nil, fmt.Errorf("invalid tag reference: %s", ref)
		}

		hostRepo := parts[0]
		tag := parts[1]

		host, repository, err := parseHostRepository(hostRepo)
		if err != nil {
			return nil, err
		}

		return &Reference{
			Host:       host,
			Repository: repository,
			Tag:        tag,
		}, nil
	}

	// Handle repository-only references (e.g., registry.com/repo)
	host, repository, err := parseHostRepository(ref)
	if err != nil {
		return nil, err
	}

	return &Reference{
		Host:       host,
		Repository: repository,
		Tag:        "latest", // Default tag
	}, nil
}

// parseHostRepository parses host and repository from a host/repository string
func parseHostRepository(hostRepo string) (string, string, error) {
	parts := strings.SplitN(hostRepo, "/", 2)
	if len(parts) != 2 {
		return "", "", fmt.Errorf("invalid host/repository format: %s", hostRepo)
	}

	host := parts[0]
	repository := parts[1]

	// Validate host (should contain at least one dot or be 'localhost')
	if !strings.Contains(host, ".") && host != "localhost" {
		// This might be a Docker Hub reference without explicit host
		return "docker.io", hostRepo, nil
	}

	return host, repository, nil
}
