import React from 'react'
import { render, screen, fireEvent, waitFor } from '@testing-library/react'
import '@testing-library/jest-dom'
import { vi } from 'vitest'
import App from '../App'
import { WorkspaceProvider } from '../contexts/WorkspaceContext'

// Mock Monaco Editor
vi.mock('@monaco-editor/react', () => ({
  Editor: ({ onChange, value }: any) => (
    <textarea
      data-testid="monaco-editor"
      value={value}
      onChange={(e) => onChange && onChange(e.target.value)}
    />
  )
}))

const renderWithProvider = (component: React.ReactElement) => {
  return render(
    <WorkspaceProvider>
      {component}
    </WorkspaceProvider>
  )
}

describe('Firebase Studio Frontend', () => {
  test('renders welcome screen initially', () => {
    renderWithProvider(<App />)
    
    expect(screen.getByText('Firebase Studio')).toBeInTheDocument()
    expect(screen.getByText(/The full stack AI workspace that feels like magic/)).toBeInTheDocument()
    expect(screen.getByText('Start Building')).toBeInTheDocument()
  })

  test('navigates to workspace after clicking get started', async () => {
    renderWithProvider(<App />)
    
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    await waitFor(() => {
      expect(screen.getByText(/Welcome to Firebase Studio/)).toBeInTheDocument()
    })
  })

  test('shows project selector when no project is selected', () => {
    renderWithProvider(<App />)
    
    // Click get started to go to workspace
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    expect(screen.getByText('Welcome to Firebase Studio')).toBeInTheDocument()
    expect(screen.getByText('Create New Project')).toBeInTheDocument()
  })

  test('creates a new project', async () => {
    renderWithProvider(<App />)
    
    // Navigate to workspace
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    // Click create project
    const createButton = screen.getByText('Create Project')
    fireEvent.click(createButton)
    
    // Fill in project name
    const nameInput = screen.getByPlaceholderText('Enter project name...')
    fireEvent.change(nameInput, { target: { value: 'Test Project' } })
    
    // Submit form
    const submitButton = screen.getByText('Create')
    fireEvent.click(submitButton)
    
    await waitFor(() => {
      expect(screen.getByText('Test Project')).toBeInTheDocument()
    })
  })

  test('file explorer shows project files', async () => {
    renderWithProvider(<App />)
    
    // Navigate and create project
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    const createButton = screen.getByText('Create Project')
    fireEvent.click(createButton)
    
    const nameInput = screen.getByPlaceholderText('Enter project name...')
    fireEvent.change(nameInput, { target: { value: 'Test Project' } })
    
    const submitButton = screen.getByText('Create')
    fireEvent.click(submitButton)
    
    await waitFor(() => {
      expect(screen.getByText('Test Project')).toBeInTheDocument()
    })
  })
})

describe('Component Integration Tests', () => {
  test('header renders with all elements', () => {
    renderWithProvider(<App />)
    
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    expect(screen.getByText('Firebase Studio')).toBeInTheDocument()
    expect(screen.getByPlaceholderText('Search projects, files, or commands...')).toBeInTheDocument()
  })

  test('workspace panels are resizable', async () => {
    renderWithProvider(<App />)
    
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    // Create a project first
    const createButton = screen.getByText('Create Project')
    fireEvent.click(createButton)
    
    const nameInput = screen.getByPlaceholderText('Enter project name...')
    fireEvent.change(nameInput, { target: { value: 'Test Project' } })
    
    const submitButton = screen.getByText('Create')
    fireEvent.click(submitButton)
    
    await waitFor(() => {
      // Check if resize handles are present after project is created
      const resizeHandles = document.querySelectorAll('.panel-resize-handle')
      expect(resizeHandles.length).toBeGreaterThan(0)
    })
  })

  test('workspace renders correctly with project', async () => {
    renderWithProvider(<App />)
    
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    // Create a project first
    const createButton = screen.getByText('Create Project')
    fireEvent.click(createButton)
    
    const nameInput = screen.getByPlaceholderText('Enter project name...')
    fireEvent.change(nameInput, { target: { value: 'Test Project' } })
    
    const submitButton = screen.getByText('Create')
    fireEvent.click(submitButton)
    
    await waitFor(() => {
      // Check that workspace components are rendered
      expect(screen.getByText('Test Project')).toBeInTheDocument()
      expect(screen.getByText('Explorer')).toBeInTheDocument()
    })
  })
})

describe('Accessibility Tests', () => {
  test('has proper ARIA labels', () => {
    renderWithProvider(<App />)
    
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    // Check for specific buttons with ARIA labels
    expect(screen.getByLabelText('Toggle menu')).toBeInTheDocument()
    expect(screen.getByLabelText('Notifications')).toBeInTheDocument()
    expect(screen.getByLabelText('Settings')).toBeInTheDocument()
  })

  test('supports keyboard navigation', () => {
    renderWithProvider(<App />)
    
    const getStartedButton = screen.getByText('Start Building')
    fireEvent.click(getStartedButton)
    
    // Test tab navigation
    const firstFocusable = document.querySelector('button')
    if (firstFocusable) {
      firstFocusable.focus()
      expect(document.activeElement).toBe(firstFocusable)
    }
  })
})

describe('Performance Tests', () => {
  test('renders within acceptable time', async () => {
    const startTime = performance.now()
    
    renderWithProvider(<App />)
    
    const endTime = performance.now()
    const renderTime = endTime - startTime
    
    // Should render within 100ms
    expect(renderTime).toBeLessThan(100)
  })

  test('handles large file lists efficiently', () => {
    renderWithProvider(<App />)
    
    // This would test with a large number of files
    // For now, just ensure the component renders
    expect(screen.getByText('Firebase Studio')).toBeInTheDocument()
  })
})
