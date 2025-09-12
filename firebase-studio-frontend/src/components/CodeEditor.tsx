import React, { useState } from 'react'
import { Editor } from '@monaco-editor/react'
import { useWorkspace } from '../contexts/WorkspaceContext'
import { 
  Save, 
  Play, 
  Terminal, 
  Settings, 
  Maximize2, 
  Minimize2,
  FileText,
  X
} from 'lucide-react'

const CodeEditor: React.FC = () => {
  const { activeFile, updateFile, isAIPanelOpen, isPreviewPanelOpen, toggleAIPanel, togglePreviewPanel } = useWorkspace()
  const [isFullscreen, setIsFullscreen] = useState(false)
  const [showTerminal, setShowTerminal] = useState(false)
  const [terminalOutput, setTerminalOutput] = useState('')

  const handleEditorChange = (value: string | undefined) => {
    if (activeFile && value !== undefined) {
      updateFile(activeFile.id, value)
    }
  }

  const getLanguage = (type: string) => {
    switch (type) {
      case 'javascript':
        return 'javascript'
      case 'typescript':
        return 'typescript'
      case 'html':
        return 'html'
      case 'css':
        return 'css'
      case 'json':
        return 'json'
      case 'python':
        return 'python'
      default:
        return 'plaintext'
    }
  }

  const handleRun = () => {
    if (!activeFile) return
    
    setTerminalOutput(`Running ${activeFile.name}...\n`)
    setShowTerminal(true)
    
    // Simulate running the code
    setTimeout(() => {
      setTerminalOutput(prev => prev + `✓ ${activeFile.name} executed successfully\n`)
    }, 1000)
  }

  const handleSave = () => {
    if (activeFile) {
      setTerminalOutput(`Saving ${activeFile.name}...\n`)
      setShowTerminal(true)
      
      setTimeout(() => {
        setTerminalOutput(prev => prev + `✓ ${activeFile.name} saved successfully\n`)
      }, 500)
    }
  }

  if (!activeFile) {
    return (
      <div className="h-full flex items-center justify-center bg-firebase-gray-50">
        <div className="text-center">
          <FileText className="w-16 h-16 text-firebase-gray-300 mx-auto mb-4" />
          <h3 className="text-lg font-medium text-firebase-gray-900 mb-2">
            No file selected
          </h3>
          <p className="text-firebase-gray-500">
            Select a file from the explorer to start editing
          </p>
        </div>
      </div>
    )
  }

  return (
    <div className="h-full flex flex-col">
      {/* Editor Header */}
      <div className="flex items-center justify-between p-3 border-b border-firebase-gray-200 bg-white">
        <div className="flex items-center space-x-3">
          <div className="flex items-center space-x-2">
            <FileText className="w-4 h-4 text-firebase-gray-600" />
            <span className="text-sm font-medium text-firebase-gray-900">
              {activeFile.name}
            </span>
          </div>
          <div className="flex items-center space-x-1">
            <button
              onClick={handleSave}
              className="p-1 hover:bg-firebase-gray-100 rounded"
              title="Save (Ctrl+S)"
              aria-label="Save file"
            >
              <Save className="w-4 h-4 text-firebase-gray-600" />
            </button>
            <button
              onClick={handleRun}
              className="p-1 hover:bg-firebase-gray-100 rounded"
              title="Run (F5)"
              aria-label="Run code"
            >
              <Play className="w-4 h-4 text-firebase-gray-600" />
            </button>
          </div>
        </div>

        <div className="flex items-center space-x-1">
          <button
            onClick={toggleAIPanel}
            className={`p-1 rounded ${
              isAIPanelOpen 
                ? 'bg-firebase-blue/10 text-firebase-blue' 
                : 'hover:bg-firebase-gray-100 text-firebase-gray-600'
            }`}
            title="Toggle AI Panel"
            aria-label="Toggle AI Panel"
          >
            <Settings className="w-4 h-4" />
          </button>
          <button
            onClick={togglePreviewPanel}
            className={`p-1 rounded ${
              isPreviewPanelOpen 
                ? 'bg-firebase-green/10 text-firebase-green' 
                : 'hover:bg-firebase-gray-100 text-firebase-gray-600'
            }`}
            title="Toggle Preview Panel"
            aria-label="Toggle Preview Panel"
          >
            <Maximize2 className="w-4 h-4" />
          </button>
          <button
            onClick={() => setShowTerminal(!showTerminal)}
            className={`p-1 rounded ${
              showTerminal 
                ? 'bg-firebase-orange/10 text-firebase-orange' 
                : 'hover:bg-firebase-gray-100 text-firebase-gray-600'
            }`}
            title="Toggle Terminal"
            aria-label="Toggle Terminal"
          >
            <Terminal className="w-4 h-4" />
          </button>
        </div>
      </div>

      {/* Editor Content */}
      <div className="flex-1 flex flex-col">
        <div className="flex-1">
          <Editor
            height="100%"
            language={getLanguage(activeFile.type)}
            value={activeFile.content}
            onChange={handleEditorChange}
            theme="vs-light"
            options={{
              minimap: { enabled: false },
              fontSize: 14,
              lineNumbers: 'on',
              roundedSelection: false,
              scrollBeyondLastLine: false,
              automaticLayout: true,
              wordWrap: 'on',
              tabSize: 2,
              insertSpaces: true,
              renderWhitespace: 'selection',
              cursorBlinking: 'smooth',
              cursorSmoothCaretAnimation: true,
              smoothScrolling: true,
              contextmenu: true,
              mouseWheelZoom: true,
              formatOnPaste: true,
              formatOnType: true,
              suggestOnTriggerCharacters: true,
              acceptSuggestionOnEnter: 'on',
              wordBasedSuggestions: true,
              parameterHints: { enabled: true },
              hover: { enabled: true },
              bracketPairColorization: { enabled: true },
              guides: {
                bracketPairs: true,
                indentation: true
              }
            }}
          />
        </div>

        {/* Terminal */}
        {showTerminal && (
          <div className="border-t border-firebase-gray-200 bg-firebase-gray-900 text-firebase-gray-100">
            <div className="flex items-center justify-between p-2 border-b border-firebase-gray-700">
              <div className="flex items-center space-x-2">
                <Terminal className="w-4 h-4" />
                <span className="text-sm font-medium">Terminal</span>
              </div>
              <button
                onClick={() => setShowTerminal(false)}
                className="p-1 hover:bg-firebase-gray-700 rounded"
              >
                <X className="w-4 h-4" />
              </button>
            </div>
            <div className="p-3 h-32 overflow-y-auto font-mono text-sm">
              <pre className="whitespace-pre-wrap">{terminalOutput}</pre>
              <div className="flex items-center space-x-2 mt-2">
                <span className="text-firebase-green">$</span>
                <input
                  type="text"
                  className="flex-1 bg-transparent border-none outline-none text-firebase-gray-100"
                  placeholder="Enter command..."
                  onKeyDown={(e) => {
                    if (e.key === 'Enter') {
                      const command = e.currentTarget.value
                      setTerminalOutput(prev => prev + `$ ${command}\n`)
                      e.currentTarget.value = ''
                    }
                  }}
                />
              </div>
            </div>
          </div>
        )}
      </div>
    </div>
  )
}

export default CodeEditor
