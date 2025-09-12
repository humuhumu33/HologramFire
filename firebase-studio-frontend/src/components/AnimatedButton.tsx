import React, { useState, useRef, useEffect } from 'react'
import { clsx } from 'clsx'

interface AnimatedButtonProps extends React.ButtonHTMLAttributes<HTMLButtonElement> {
  variant?: 'primary' | 'secondary' | 'ghost' | 'danger'
  size?: 'sm' | 'md' | 'lg'
  loading?: boolean
  icon?: React.ReactNode
  children: React.ReactNode
  ripple?: boolean
}

const AnimatedButton: React.FC<AnimatedButtonProps> = ({
  variant = 'primary',
  size = 'md',
  loading = false,
  icon,
  children,
  ripple = true,
  className,
  onClick,
  disabled,
  ...props
}) => {
  const [ripples, setRipples] = useState<Array<{ id: number; x: number; y: number }>>([])
  const buttonRef = useRef<HTMLButtonElement>(null)

  const handleClick = (e: React.MouseEvent<HTMLButtonElement>) => {
    if (ripple && buttonRef.current) {
      const rect = buttonRef.current.getBoundingClientRect()
      const x = e.clientX - rect.left
      const y = e.clientY - rect.top
      
      const newRipple = {
        id: Date.now(),
        x,
        y
      }
      
      setRipples(prev => [...prev, newRipple])
      
      // Remove ripple after animation
      setTimeout(() => {
        setRipples(prev => prev.filter(ripple => ripple.id !== newRipple.id))
      }, 600)
    }
    
    if (onClick && !loading && !disabled) {
      onClick(e)
    }
  }

  const baseClasses = 'relative overflow-hidden font-medium transition-all duration-300 ease-out focus:outline-none focus:ring-2 focus:ring-offset-2 transform active:scale-95'
  
  const variantClasses = {
    primary: 'firebase-button-primary',
    secondary: 'firebase-button-secondary',
    ghost: 'firebase-button-ghost',
    danger: 'bg-firebase-red text-white hover:bg-red-600 focus:ring-firebase-red shadow-lg hover:shadow-xl'
  }
  
  const sizeClasses = {
    sm: 'px-3 py-2 text-sm rounded-lg',
    md: 'px-4 py-2 text-base rounded-xl',
    lg: 'px-6 py-3 text-lg rounded-xl'
  }

  return (
    <button
      ref={buttonRef}
      className={clsx(
        baseClasses,
        variantClasses[variant],
        sizeClasses[size],
        loading && 'cursor-not-allowed opacity-75',
        disabled && 'cursor-not-allowed opacity-50',
        className
      )}
      onClick={handleClick}
      disabled={disabled || loading}
      {...props}
    >
      {/* Ripple Effects */}
      {ripples.map(ripple => (
        <span
          key={ripple.id}
          className="absolute pointer-events-none animate-ping"
          style={{
            left: ripple.x - 10,
            top: ripple.y - 10,
            width: 20,
            height: 20,
            borderRadius: '50%',
            backgroundColor: 'rgba(255, 255, 255, 0.6)',
            animation: 'ripple 0.6s ease-out'
          }}
        />
      ))}
      
      {/* Loading Spinner */}
      {loading && (
        <div className="absolute inset-0 flex items-center justify-center">
          <div className="w-5 h-5 border-2 border-white border-t-transparent rounded-full animate-spin" />
        </div>
      )}
      
      {/* Button Content */}
      <div className={clsx('flex items-center justify-center space-x-2', loading && 'opacity-0')}>
        {icon && <span className="flex-shrink-0">{icon}</span>}
        <span>{children}</span>
      </div>
      
      <style jsx>{`
        @keyframes ripple {
          0% {
            transform: scale(0);
            opacity: 1;
          }
          100% {
            transform: scale(4);
            opacity: 0;
          }
        }
      `}</style>
    </button>
  )
}

export default AnimatedButton
