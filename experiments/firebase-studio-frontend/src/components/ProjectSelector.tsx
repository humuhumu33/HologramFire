import React, { useState } from 'react'
import { useWorkspace } from '../contexts/WorkspaceContext'
import { createDemoProject } from '../utils/demoProjects'
import { Plus, FolderOpen, Github, Gitlab, Upload, Sparkles } from 'lucide-react'

const ProjectSelector: React.FC = () => {
  const { projects, createProject, selectProject } = useWorkspace()
  const [showCreateForm, setShowCreateForm] = useState(false)
  const [projectName, setProjectName] = useState('')

  const handleCreateProject = () => {
    if (projectName.trim()) {
      createProject(projectName.trim())
      setProjectName('')
      setShowCreateForm(false)
    }
  }

  const handleImportFromGit = (provider: 'github' | 'gitlab') => {
    // This would integrate with the actual import functionality
    console.log(`Importing from ${provider}`)
  }

  const handleUploadProject = () => {
    // This would handle file upload
    console.log('Uploading project')
  }

  const handleCreateDemo = () => {
    const demoProject = createDemoProject()
    // Add demo project to the workspace
    createProject(demoProject.name)
    // Note: In a real implementation, we'd need to add the demo files to the project
  }

  return (
    <div className="h-full flex items-center justify-center p-8">
      <div className="max-w-4xl w-full">
        <div className="text-center mb-12">
          <div className="w-20 h-20 bg-firebase-blue rounded-2xl flex items-center justify-center mx-auto mb-6">
            <Sparkles className="w-10 h-10 text-white" />
          </div>
          <h1 className="text-3xl font-bold text-firebase-gray-900 mb-4">
            Welcome to Firebase Studio
          </h1>
          <p className="text-firebase-gray-600 text-lg">
            Create a new project or import an existing one to get started
          </p>
        </div>

        <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-6">
          {/* Create New Project */}
          <div className="firebase-card p-6 hover:shadow-lg transition-all duration-200 cursor-pointer group">
            <div className="w-12 h-12 bg-firebase-blue/10 rounded-xl flex items-center justify-center mb-4 group-hover:bg-firebase-blue/20 transition-colors">
              <Plus className="w-6 h-6 text-firebase-blue" />
            </div>
            <h3 className="font-semibold text-firebase-gray-900 mb-2">Create New Project</h3>
            <p className="text-firebase-gray-600 text-sm mb-4">
              Start with a blank project and build from scratch
            </p>
            <button
              onClick={() => setShowCreateForm(true)}
              className="firebase-button-primary w-full"
            >
              Create Project
            </button>
          </div>

          {/* Import from GitHub */}
          <div className="firebase-card p-6 hover:shadow-lg transition-all duration-200 cursor-pointer group">
            <div className="w-12 h-12 bg-firebase-gray-100 rounded-xl flex items-center justify-center mb-4 group-hover:bg-firebase-gray-200 transition-colors">
              <Github className="w-6 h-6 text-firebase-gray-700" />
            </div>
            <h3 className="font-semibold text-firebase-gray-900 mb-2">Import from GitHub</h3>
            <p className="text-firebase-gray-600 text-sm mb-4">
              Clone and work with your existing GitHub repositories
            </p>
            <button
              onClick={() => handleImportFromGit('github')}
              className="firebase-button-secondary w-full"
            >
              Import from GitHub
            </button>
          </div>

          {/* Import from GitLab */}
          <div className="firebase-card p-6 hover:shadow-lg transition-all duration-200 cursor-pointer group">
            <div className="w-12 h-12 bg-firebase-orange/10 rounded-xl flex items-center justify-center mb-4 group-hover:bg-firebase-orange/20 transition-colors">
              <Gitlab className="w-6 h-6 text-firebase-orange" />
            </div>
            <h3 className="font-semibold text-firebase-gray-900 mb-2">Import from GitLab</h3>
            <p className="text-firebase-gray-600 text-sm mb-4">
              Import your GitLab projects and continue development
            </p>
            <button
              onClick={() => handleImportFromGit('gitlab')}
              className="firebase-button-secondary w-full"
            >
              Import from GitLab
            </button>
          </div>

          {/* Upload Project */}
          <div className="firebase-card p-6 hover:shadow-lg transition-all duration-200 cursor-pointer group">
            <div className="w-12 h-12 bg-firebase-green/10 rounded-xl flex items-center justify-center mb-4 group-hover:bg-firebase-green/20 transition-colors">
              <Upload className="w-6 h-6 text-firebase-green" />
            </div>
            <h3 className="font-semibold text-firebase-gray-900 mb-2">Upload Project</h3>
            <p className="text-firebase-gray-600 text-sm mb-4">
              Upload a local project folder or zip file
            </p>
            <button
              onClick={handleUploadProject}
              className="firebase-button-secondary w-full"
            >
              Upload Project
            </button>
          </div>

          {/* Browse Templates */}
          <div className="firebase-card p-6 hover:shadow-lg transition-all duration-200 cursor-pointer group">
            <div className="w-12 h-12 bg-firebase-yellow/10 rounded-xl flex items-center justify-center mb-4 group-hover:bg-firebase-yellow/20 transition-colors">
              <FolderOpen className="w-6 h-6 text-firebase-yellow" />
            </div>
            <h3 className="font-semibold text-firebase-gray-900 mb-2">Browse Templates</h3>
            <p className="text-firebase-gray-600 text-sm mb-4">
              Start with popular framework templates
            </p>
            <button className="firebase-button-secondary w-full">
              Browse Templates
            </button>
          </div>

          {/* Demo Project */}
          <div className="firebase-card p-6 hover:shadow-lg transition-all duration-200 cursor-pointer group">
            <div className="w-12 h-12 bg-firebase-blue/10 rounded-xl flex items-center justify-center mb-4 group-hover:bg-firebase-blue/20 transition-colors">
              <Sparkles className="w-6 h-6 text-firebase-blue" />
            </div>
            <h3 className="font-semibold text-firebase-gray-900 mb-2">Try Demo Project</h3>
            <p className="text-firebase-gray-600 text-sm mb-4">
              Explore Firebase Studio with a pre-built demo
            </p>
            <button
              onClick={handleCreateDemo}
              className="firebase-button-primary w-full"
            >
              Load Demo
            </button>
          </div>
        </div>

        {/* Recent Projects */}
        {projects.length > 0 && (
          <div className="mt-12">
            <h2 className="text-xl font-semibold text-firebase-gray-900 mb-6">Recent Projects</h2>
            <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-4">
              {projects.map((project) => (
                <div
                  key={project.id}
                  className="firebase-card p-4 hover:shadow-md transition-all duration-200 cursor-pointer"
                >
                  <div className="flex items-center space-x-3">
                    <div className="w-10 h-10 bg-firebase-blue/10 rounded-lg flex items-center justify-center">
                      <FolderOpen className="w-5 h-5 text-firebase-blue" />
                    </div>
                    <div className="flex-1 min-w-0">
                      <h3 className="font-medium text-firebase-gray-900 truncate">
                        {project.name}
                      </h3>
                      <p className="text-firebase-gray-500 text-sm">
                        {project.files.length} files
                      </p>
                    </div>
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}
      </div>

      {/* Create Project Modal */}
      {showCreateForm && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50">
          <div className="bg-white rounded-2xl p-6 w-full max-w-md mx-4">
            <h2 className="text-xl font-semibold text-firebase-gray-900 mb-4">
              Create New Project
            </h2>
            <div className="mb-6">
              <label className="block text-sm font-medium text-firebase-gray-700 mb-2">
                Project Name
              </label>
              <input
                type="text"
                value={projectName}
                onChange={(e) => setProjectName(e.target.value)}
                placeholder="Enter project name..."
                className="w-full px-3 py-2 border border-firebase-gray-300 rounded-lg focus:outline-none focus:ring-2 focus:ring-firebase-blue focus:border-transparent"
                autoFocus
              />
            </div>
            <div className="flex space-x-3">
              <button
                onClick={() => setShowCreateForm(false)}
                className="firebase-button-secondary flex-1"
              >
                Cancel
              </button>
              <button
                onClick={handleCreateProject}
                className="firebase-button-primary flex-1"
                disabled={!projectName.trim()}
              >
                Create
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  )
}

export default ProjectSelector
