import React, { useState } from 'react'
import { useWorkspace } from '../contexts/WorkspaceContext'
import { 
  Folder, 
  File, 
  Plus, 
  MoreVertical, 
  ChevronRight, 
  ChevronDown,
  FileText,
  FileCode,
  FileImage,
  FileJson
} from 'lucide-react'

const FileExplorer: React.FC = () => {
  const { currentProject, activeFile, selectFile, createFile, deleteFile } = useWorkspace()
  const [expandedFolders, setExpandedFolders] = useState<Set<string>>(new Set(['root']))
  const [showCreateMenu, setShowCreateMenu] = useState(false)
  const [createMenuPosition, setCreateMenuPosition] = useState({ x: 0, y: 0 })

  if (!currentProject) {
    return (
      <div className="h-full flex items-center justify-center text-firebase-gray-500">
        No project selected
      </div>
    )
  }

  const toggleFolder = (folderId: string) => {
    const newExpanded = new Set(expandedFolders)
    if (newExpanded.has(folderId)) {
      newExpanded.delete(folderId)
    } else {
      newExpanded.add(folderId)
    }
    setExpandedFolders(newExpanded)
  }

  const getFileIcon = (type: string) => {
    switch (type) {
      case 'javascript':
      case 'typescript':
        return <FileCode className="w-4 h-4 text-firebase-yellow" />
      case 'html':
      case 'css':
        return <FileCode className="w-4 h-4 text-firebase-orange" />
      case 'json':
        return <FileJson className="w-4 h-4 text-firebase-green" />
      case 'python':
        return <FileCode className="w-4 h-4 text-firebase-blue" />
      default:
        return <FileText className="w-4 h-4 text-firebase-gray-500" />
    }
  }

  const handleCreateFile = (type: string) => {
    const name = prompt(`Enter ${type} file name:`)
    if (name) {
      createFile(name, type as any)
    }
    setShowCreateMenu(false)
  }

  const handleContextMenu = (e: React.MouseEvent, fileId?: string) => {
    e.preventDefault()
    setCreateMenuPosition({ x: e.clientX, y: e.clientY })
    setShowCreateMenu(true)
  }

  const handleDeleteFile = (fileId: string) => {
    if (confirm('Are you sure you want to delete this file?')) {
      deleteFile(fileId)
    }
  }

  return (
    <div className="h-full flex flex-col">
      {/* Header */}
      <div className="p-4 border-b border-firebase-gray-200">
        <div className="flex items-center justify-between">
          <h2 className="font-semibold text-firebase-gray-900">Explorer</h2>
          <button
            onClick={() => setShowCreateMenu(true)}
            className="p-1 hover:bg-firebase-gray-100 rounded"
            aria-label="Create new file"
          >
            <Plus className="w-4 h-4 text-firebase-gray-600" />
          </button>
        </div>
      </div>

      {/* File Tree */}
      <div className="flex-1 overflow-y-auto p-2">
        <div className="space-y-1">
          {/* Root Folder */}
          <div>
            <div
              className="flex items-center space-x-2 p-2 hover:bg-firebase-gray-100 rounded cursor-pointer"
              onClick={() => toggleFolder('root')}
            >
              {expandedFolders.has('root') ? (
                <ChevronDown className="w-4 h-4 text-firebase-gray-500" />
              ) : (
                <ChevronRight className="w-4 h-4 text-firebase-gray-500" />
              )}
              <Folder className="w-4 h-4 text-firebase-blue" />
              <span className="text-sm font-medium text-firebase-gray-900">
                {currentProject.name}
              </span>
            </div>

            {/* Files */}
            {expandedFolders.has('root') && (
              <div className="ml-6 space-y-1">
                {currentProject.files.map((file) => (
                  <div
                    key={file.id}
                    className={`flex items-center space-x-2 p-2 rounded cursor-pointer group ${
                      activeFile?.id === file.id
                        ? 'bg-firebase-blue/10 text-firebase-blue'
                        : 'hover:bg-firebase-gray-100'
                    }`}
                    onClick={() => selectFile(file.id)}
                    onContextMenu={(e) => handleContextMenu(e, file.id)}
                  >
                    {getFileIcon(file.type)}
                    <span className="text-sm text-firebase-gray-900 flex-1">
                      {file.name}
                    </span>
                    <button
                      onClick={(e) => {
                        e.stopPropagation()
                        handleDeleteFile(file.id)
                      }}
                      className="opacity-0 group-hover:opacity-100 p-1 hover:bg-firebase-gray-200 rounded"
                    >
                      <MoreVertical className="w-3 h-3 text-firebase-gray-500" />
                    </button>
                  </div>
                ))}
              </div>
            )}
          </div>
        </div>
      </div>

      {/* Create File Menu */}
      {showCreateMenu && (
        <div
          className="fixed bg-white border border-firebase-gray-200 rounded-lg shadow-lg py-2 z-50"
          style={{
            left: createMenuPosition.x,
            top: createMenuPosition.y,
          }}
        >
          <button
            onClick={() => handleCreateFile('javascript')}
            className="w-full px-4 py-2 text-left hover:bg-firebase-gray-100 text-sm"
          >
            JavaScript File
          </button>
          <button
            onClick={() => handleCreateFile('typescript')}
            className="w-full px-4 py-2 text-left hover:bg-firebase-gray-100 text-sm"
          >
            TypeScript File
          </button>
          <button
            onClick={() => handleCreateFile('html')}
            className="w-full px-4 py-2 text-left hover:bg-firebase-gray-100 text-sm"
          >
            HTML File
          </button>
          <button
            onClick={() => handleCreateFile('css')}
            className="w-full px-4 py-2 text-left hover:bg-firebase-gray-100 text-sm"
          >
            CSS File
          </button>
          <button
            onClick={() => handleCreateFile('json')}
            className="w-full px-4 py-2 text-left hover:bg-firebase-gray-100 text-sm"
          >
            JSON File
          </button>
          <button
            onClick={() => handleCreateFile('python')}
            className="w-full px-4 py-2 text-left hover:bg-firebase-gray-100 text-sm"
          >
            Python File
          </button>
        </div>
      )}

      {/* Click outside to close menu */}
      {showCreateMenu && (
        <div
          className="fixed inset-0 z-40"
          onClick={() => setShowCreateMenu(false)}
        />
      )}
    </div>
  )
}

export default FileExplorer
