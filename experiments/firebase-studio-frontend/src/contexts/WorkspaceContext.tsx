import React, { createContext, useContext, useState, ReactNode } from 'react'

interface WorkspaceFile {
  id: string
  name: string
  content: string
  type: 'javascript' | 'typescript' | 'python' | 'html' | 'css' | 'json'
  path: string
}

interface WorkspaceProject {
  id: string
  name: string
  files: WorkspaceFile[]
  createdAt: Date
  updatedAt: Date
}

interface WorkspaceContextType {
  currentProject: WorkspaceProject | null
  projects: WorkspaceProject[]
  activeFile: WorkspaceFile | null
  isAIPanelOpen: boolean
  isPreviewPanelOpen: boolean
  panelSizes: {
    left: number
    center: number
    right: number
  }
  
  // Actions
  createProject: (name: string) => void
  selectProject: (projectId: string) => void
  createFile: (name: string, type: WorkspaceFile['type'], content?: string) => void
  selectFile: (fileId: string) => void
  updateFile: (fileId: string, content: string) => void
  deleteFile: (fileId: string) => void
  toggleAIPanel: () => void
  togglePreviewPanel: () => void
  updatePanelSizes: (sizes: Partial<WorkspaceContextType['panelSizes']>) => void
}

const WorkspaceContext = createContext<WorkspaceContextType | undefined>(undefined)

export const useWorkspace = () => {
  const context = useContext(WorkspaceContext)
  if (!context) {
    throw new Error('useWorkspace must be used within a WorkspaceProvider')
  }
  return context
}

interface WorkspaceProviderProps {
  children: ReactNode
}

export const WorkspaceProvider: React.FC<WorkspaceProviderProps> = ({ children }) => {
  const [projects, setProjects] = useState<WorkspaceProject[]>([])
  const [currentProject, setCurrentProject] = useState<WorkspaceProject | null>(null)
  const [activeFile, setActiveFile] = useState<WorkspaceFile | null>(null)
  const [isAIPanelOpen, setIsAIPanelOpen] = useState(true)
  const [isPreviewPanelOpen, setIsPreviewPanelOpen] = useState(true)
  const [panelSizes, setPanelSizes] = useState({
    left: 300,
    center: 600,
    right: 300
  })

  const createProject = (name: string) => {
    const newProject: WorkspaceProject = {
      id: Date.now().toString(),
      name,
      files: [],
      createdAt: new Date(),
      updatedAt: new Date()
    }
    
    setProjects(prev => [...prev, newProject])
    setCurrentProject(newProject)
  }

  const selectProject = (projectId: string) => {
    const project = projects.find(p => p.id === projectId)
    if (project) {
      setCurrentProject(project)
      setActiveFile(project.files[0] || null)
    }
  }

  const createFile = (name: string, type: WorkspaceFile['type'], content = '') => {
    if (!currentProject) return

    const newFile: WorkspaceFile = {
      id: Date.now().toString(),
      name,
      content,
      type,
      path: `/${name}`
    }

    const updatedProject = {
      ...currentProject,
      files: [...currentProject.files, newFile],
      updatedAt: new Date()
    }

    setProjects(prev => prev.map(p => p.id === currentProject.id ? updatedProject : p))
    setCurrentProject(updatedProject)
    setActiveFile(newFile)
  }

  const selectFile = (fileId: string) => {
    if (!currentProject) return
    
    const file = currentProject.files.find(f => f.id === fileId)
    if (file) {
      setActiveFile(file)
    }
  }

  const updateFile = (fileId: string, content: string) => {
    if (!currentProject) return

    const updatedProject = {
      ...currentProject,
      files: currentProject.files.map(f => 
        f.id === fileId ? { ...f, content } : f
      ),
      updatedAt: new Date()
    }

    setProjects(prev => prev.map(p => p.id === currentProject.id ? updatedProject : p))
    setCurrentProject(updatedProject)
    setActiveFile(prev => prev?.id === fileId ? { ...prev, content } : prev)
  }

  const deleteFile = (fileId: string) => {
    if (!currentProject) return

    const updatedProject = {
      ...currentProject,
      files: currentProject.files.filter(f => f.id !== fileId),
      updatedAt: new Date()
    }

    setProjects(prev => prev.map(p => p.id === currentProject.id ? updatedProject : p))
    setCurrentProject(updatedProject)
    
    if (activeFile?.id === fileId) {
      setActiveFile(updatedProject.files[0] || null)
    }
  }

  const toggleAIPanel = () => {
    setIsAIPanelOpen(prev => !prev)
  }

  const togglePreviewPanel = () => {
    setIsPreviewPanelOpen(prev => !prev)
  }

  const updatePanelSizes = (sizes: Partial<WorkspaceContextType['panelSizes']>) => {
    setPanelSizes(prev => ({ ...prev, ...sizes }))
  }

  const value: WorkspaceContextType = {
    currentProject,
    projects,
    activeFile,
    isAIPanelOpen,
    isPreviewPanelOpen,
    panelSizes,
    createProject,
    selectProject,
    createFile,
    selectFile,
    updateFile,
    deleteFile,
    toggleAIPanel,
    togglePreviewPanel,
    updatePanelSizes
  }

  return (
    <WorkspaceContext.Provider value={value}>
      {children}
    </WorkspaceContext.Provider>
  )
}
