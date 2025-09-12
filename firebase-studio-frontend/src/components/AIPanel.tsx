import React, { useState, useRef, useEffect } from 'react'
import { 
  Send, 
  Bot, 
  User, 
  Sparkles, 
  Code, 
  Bug, 
  FileText, 
  Lightbulb,
  Copy,
  ThumbsUp,
  ThumbsDown,
  RotateCcw
} from 'lucide-react'

interface Message {
  id: string
  type: 'user' | 'assistant'
  content: string
  timestamp: Date
}

const AIPanel: React.FC = () => {
  const [messages, setMessages] = useState<Message[]>([
    {
      id: '1',
      type: 'assistant',
      content: 'Hello! I\'m your AI coding assistant. I can help you with coding, debugging, testing, refactoring, explaining, and documenting code. What would you like to work on today?',
      timestamp: new Date()
    }
  ])
  const [input, setInput] = useState('')
  const [isLoading, setIsLoading] = useState(false)
  const messagesEndRef = useRef<HTMLDivElement>(null)

  const scrollToBottom = () => {
    if (messagesEndRef.current && typeof messagesEndRef.current.scrollIntoView === 'function') {
      messagesEndRef.current.scrollIntoView({ behavior: 'smooth' })
    }
  }

  useEffect(() => {
    scrollToBottom()
  }, [messages])

  const handleSend = async () => {
    if (!input.trim() || isLoading) return

    const userMessage: Message = {
      id: Date.now().toString(),
      type: 'user',
      content: input.trim(),
      timestamp: new Date()
    }

    setMessages(prev => [...prev, userMessage])
    setInput('')
    setIsLoading(true)

    // Simulate AI response
    setTimeout(() => {
      const assistantMessage: Message = {
        id: (Date.now() + 1).toString(),
        type: 'assistant',
        content: generateAIResponse(userMessage.content),
        timestamp: new Date()
      }
      setMessages(prev => [...prev, assistantMessage])
      setIsLoading(false)
    }, 1500)
  }

  const generateAIResponse = (userInput: string): string => {
    const lowerInput = userInput.toLowerCase()
    
    if (lowerInput.includes('hello') || lowerInput.includes('hi')) {
      return 'Hello! I\'m here to help you with your coding tasks. I can assist with writing code, debugging, explaining concepts, refactoring, and more. What specific task would you like help with?'
    }
    
    if (lowerInput.includes('bug') || lowerInput.includes('error')) {
      return 'I can help you debug your code! Please share the error message or describe the issue you\'re experiencing. I can analyze the code, identify potential problems, and suggest solutions.'
    }
    
    if (lowerInput.includes('explain') || lowerInput.includes('how')) {
      return 'I\'d be happy to explain! Please provide the code snippet or concept you\'d like me to explain, and I\'ll break it down in detail with examples.'
    }
    
    if (lowerInput.includes('refactor') || lowerInput.includes('improve')) {
      return 'I can help you refactor and improve your code! Share the code you\'d like to refactor, and I\'ll suggest improvements for readability, performance, and best practices.'
    }
    
    if (lowerInput.includes('test') || lowerInput.includes('testing')) {
      return 'I can help you write tests! Whether you need unit tests, integration tests, or test strategies, I can generate test code and explain testing best practices.'
    }
    
    return 'I understand you\'re asking about: "' + userInput + '". I can help you with coding, debugging, testing, refactoring, explaining code, and more. Could you provide more specific details about what you\'d like me to help you with?'
  }

  const handleKeyPress = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault()
      handleSend()
    }
  }

  const copyToClipboard = (text: string) => {
    navigator.clipboard.writeText(text)
  }

  const quickActions = [
    { icon: <Code className="w-4 h-4" />, label: 'Write Code', prompt: 'Help me write a function that...' },
    { icon: <Bug className="w-4 h-4" />, label: 'Debug', prompt: 'I have a bug in my code...' },
    { icon: <FileText className="w-4 h-4" />, label: 'Explain', prompt: 'Can you explain this code...' },
    { icon: <Lightbulb className="w-4 h-4" />, label: 'Refactor', prompt: 'How can I improve this code...' }
  ]

  return (
    <div className="h-full flex flex-col">
      {/* Header */}
      <div className="p-4 border-b border-firebase-gray-200 bg-white">
        <div className="flex items-center space-x-2">
          <div className="w-8 h-8 bg-firebase-blue/10 rounded-lg flex items-center justify-center">
            <Bot className="w-5 h-5 text-firebase-blue" />
          </div>
          <div>
            <h3 className="font-semibold text-firebase-gray-900">Gemini AI</h3>
            <p className="text-xs text-firebase-gray-500">Your coding assistant</p>
          </div>
        </div>
      </div>

      {/* Quick Actions */}
      <div className="p-3 border-b border-firebase-gray-200 bg-firebase-gray-50">
        <div className="grid grid-cols-2 gap-2">
          {quickActions.map((action, index) => (
            <button
              key={index}
              onClick={() => setInput(action.prompt)}
              className="flex items-center space-x-2 p-2 text-left hover:bg-white rounded-lg transition-colors"
            >
              {action.icon}
              <span className="text-sm text-firebase-gray-700">{action.label}</span>
            </button>
          ))}
        </div>
      </div>

      {/* Messages */}
      <div className="flex-1 overflow-y-auto p-4 space-y-4">
        {messages.map((message) => (
          <div
            key={message.id}
            className={`flex ${message.type === 'user' ? 'justify-end' : 'justify-start'}`}
          >
            <div
              className={`max-w-[80%] rounded-lg p-3 ${
                message.type === 'user'
                  ? 'bg-firebase-blue text-white'
                  : 'bg-firebase-gray-100 text-firebase-gray-900'
              }`}
            >
              <div className="flex items-start space-x-2">
                {message.type === 'assistant' && (
                  <Bot className="w-4 h-4 mt-0.5 text-firebase-blue flex-shrink-0" />
                )}
                {message.type === 'user' && (
                  <User className="w-4 h-4 mt-0.5 text-white flex-shrink-0" />
                )}
                <div className="flex-1">
                  <p className="text-sm whitespace-pre-wrap">{message.content}</p>
                  {message.type === 'assistant' && (
                    <div className="flex items-center space-x-2 mt-2">
                      <button
                        onClick={() => copyToClipboard(message.content)}
                        className="p-1 hover:bg-firebase-gray-200 rounded"
                        title="Copy"
                      >
                        <Copy className="w-3 h-3 text-firebase-gray-500" />
                      </button>
                      <button
                        className="p-1 hover:bg-firebase-gray-200 rounded"
                        title="Good response"
                      >
                        <ThumbsUp className="w-3 h-3 text-firebase-gray-500" />
                      </button>
                      <button
                        className="p-1 hover:bg-firebase-gray-200 rounded"
                        title="Poor response"
                      >
                        <ThumbsDown className="w-3 h-3 text-firebase-gray-500" />
                      </button>
                    </div>
                  )}
                </div>
              </div>
            </div>
          </div>
        ))}
        
        {isLoading && (
          <div className="flex justify-start">
            <div className="bg-firebase-gray-100 rounded-lg p-3">
              <div className="flex items-center space-x-2">
                <Bot className="w-4 h-4 text-firebase-blue" />
                <div className="flex space-x-1">
                  <div className="w-2 h-2 bg-firebase-gray-400 rounded-full animate-bounce"></div>
                  <div className="w-2 h-2 bg-firebase-gray-400 rounded-full animate-bounce" style={{ animationDelay: '0.1s' }}></div>
                  <div className="w-2 h-2 bg-firebase-gray-400 rounded-full animate-bounce" style={{ animationDelay: '0.2s' }}></div>
                </div>
              </div>
            </div>
          </div>
        )}
        
        <div ref={messagesEndRef} />
      </div>

      {/* Input */}
      <div className="p-4 border-t border-firebase-gray-200 bg-white">
        <div className="flex space-x-2">
          <div className="flex-1 relative">
            <textarea
              value={input}
              onChange={(e) => setInput(e.target.value)}
              onKeyPress={handleKeyPress}
              placeholder="Ask me anything about coding..."
              className="w-full p-3 border border-firebase-gray-300 rounded-lg focus:outline-none focus:ring-2 focus:ring-firebase-blue focus:border-transparent resize-none"
              rows={2}
              disabled={isLoading}
            />
          </div>
          <button
            onClick={handleSend}
            disabled={!input.trim() || isLoading}
            className="firebase-button-primary px-4 py-3 disabled:opacity-50 disabled:cursor-not-allowed"
          >
            <Send className="w-4 h-4" />
          </button>
        </div>
        <div className="flex items-center justify-between mt-2">
          <p className="text-xs text-firebase-gray-500">
            Press Enter to send, Shift+Enter for new line
          </p>
          <button
            onClick={() => setMessages([messages[0]])}
            className="flex items-center space-x-1 text-xs text-firebase-gray-500 hover:text-firebase-gray-700"
          >
            <RotateCcw className="w-3 h-3" />
            <span>Clear chat</span>
          </button>
        </div>
      </div>
    </div>
  )
}

export default AIPanel
