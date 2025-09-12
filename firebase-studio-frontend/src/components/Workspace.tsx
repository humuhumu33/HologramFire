import React, { useState, useRef, useEffect } from 'react'
import { useWorkspace } from '../contexts/WorkspaceContext'
import FileExplorer from './FileExplorer'
import CodeEditor from './CodeEditor'
import AIPanel from './AIPanel'
import PreviewPanel from './PreviewPanel'
import ProjectSelector from './ProjectSelector'

const Workspace: React.FC = () => {
  const { 
    isAIPanelOpen, 
    isPreviewPanelOpen, 
    panelSizes, 
    updatePanelSizes,
    currentProject 
  } = useWorkspace()
  
  const [isResizing, setIsResizing] = useState(false)
  const [resizeStartX, setResizeStartX] = useState(0)
  const [resizeStartSizes, setResizeStartSizes] = useState(panelSizes)
  const containerRef = useRef<HTMLDivElement>(null)

  const handleMouseDown = (e: React.MouseEvent) => {
    setIsResizing(true)
    setResizeStartX(e.clientX)
    setResizeStartSizes(panelSizes)
    document.body.style.cursor = 'col-resize'
    document.body.style.userSelect = 'none'
  }

  const handleMouseMove = (e: MouseEvent) => {
    if (!isResizing || !containerRef.current) return

    const deltaX = e.clientX - resizeStartX
    const containerWidth = containerRef.current.offsetWidth
    const totalSize = panelSizes.left + panelSizes.center + panelSizes.right

    // Calculate new sizes
    const newLeft = Math.max(200, Math.min(600, resizeStartSizes.left + deltaX))
    const newCenter = Math.max(400, panelSizes.center - (newLeft - resizeStartSizes.left))
    const newRight = Math.max(200, panelSizes.right)

    updatePanelSizes({
      left: newLeft,
      center: newCenter,
      right: newRight
    })
  }

  const handleMouseUp = () => {
    setIsResizing(false)
    document.body.style.cursor = ''
    document.body.style.userSelect = ''
  }

  useEffect(() => {
    if (isResizing) {
      document.addEventListener('mousemove', handleMouseMove)
      document.addEventListener('mouseup', handleMouseUp)
      return () => {
        document.removeEventListener('mousemove', handleMouseMove)
        document.removeEventListener('mouseup', handleMouseUp)
      }
    }
  }, [isResizing, resizeStartX, resizeStartSizes])

  if (!currentProject) {
    return <ProjectSelector />
  }

  return (
    <div 
      ref={containerRef}
      className="flex h-[calc(100vh-88px)] bg-firebase-gray-50 relative"
    >
      {/* Mobile/Tablet Overlay for Panel Controls */}
      <div className="lg:hidden fixed top-20 left-4 z-30 flex flex-col space-y-2">
        <button 
          className="p-3 bg-white rounded-xl shadow-lg border border-firebase-gray-200 hover:shadow-xl transition-all duration-200"
          onClick={() => updatePanelSizes({ ...panelSizes, left: panelSizes.left > 0 ? 0 : 300 })}
        >
          <svg className="w-5 h-5 text-firebase-gray-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 6h16M4 12h16M4 18h16" />
          </svg>
        </button>
        <button 
          className="p-3 bg-white rounded-xl shadow-lg border border-firebase-gray-200 hover:shadow-xl transition-all duration-200"
          onClick={() => updatePanelSizes({ ...panelSizes, right: panelSizes.right > 0 ? 0 : 300 })}
        >
          <svg className="w-5 h-5 text-firebase-gray-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 5H7a2 2 0 00-2 2v10a2 2 0 002 2h8a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2" />
          </svg>
        </button>
      </div>

      {/* Left Panel - File Explorer */}
      <div 
        className={`bg-white border-r border-firebase-gray-200 flex-shrink-0 transition-all duration-300 ease-out ${
          panelSizes.left > 0 ? 'translate-x-0' : '-translate-x-full lg:translate-x-0'
        } lg:relative absolute left-0 top-0 h-full z-20 shadow-xl lg:shadow-none`}
        style={{ width: panelSizes.left || 300 }}
      >
        <FileExplorer />
      </div>

      {/* Resize Handle - Desktop Only */}
      <div
        className="panel-resize-handle flex-shrink-0 hidden lg:block"
        onMouseDown={handleMouseDown}
      />

      {/* Center Panel - Code Editor */}
      <div 
        className="bg-white flex-shrink-0 flex-1 min-w-0"
        style={{ width: panelSizes.center }}
      >
        <CodeEditor />
      </div>

      {/* Resize Handle - Desktop Only */}
      {isPreviewPanelOpen && (
        <div
          className="panel-resize-handle flex-shrink-0 hidden lg:block"
          onMouseDown={handleMouseDown}
        />
      )}

      {/* Right Panel - AI and Preview */}
      {isPreviewPanelOpen && (
        <div 
          className={`bg-white border-l border-firebase-gray-200 flex-shrink-0 transition-all duration-300 ease-out ${
            panelSizes.right > 0 ? 'translate-x-0' : 'translate-x-full lg:translate-x-0'
          } lg:relative absolute right-0 top-0 h-full z-20 shadow-xl lg:shadow-none`}
          style={{ width: panelSizes.right || 300 }}
        >
          <div className="h-full flex flex-col">
            {isAIPanelOpen && (
              <>
                <div className="flex-1">
                  <AIPanel />
                </div>
                <div className="h-px bg-firebase-gray-200"></div>
              </>
            )}
            <div className="flex-1">
              <PreviewPanel />
            </div>
          </div>
        </div>
      )}

      {/* Mobile Overlay */}
      {(panelSizes.left > 0 || panelSizes.right > 0) && (
        <div 
          className="lg:hidden fixed inset-0 bg-black/50 z-10"
          onClick={() => {
            updatePanelSizes({ ...panelSizes, left: 0, right: 0 })
          }}
        />
      )}
    </div>
  )
}

export default Workspace
