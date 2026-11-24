import React from 'react'
import { useNavigate, useLocation } from 'react-router-dom'
import { Card, Badge, Button } from '../components/UI'

export default function NotFound() {
  const navigate = useNavigate()
  const location = useLocation()

  return (
    <div className="py-12 max-w-lg mx-auto">
      <Card>
        <div className="text-center space-y-4 py-4">
          <Badge active>404 · Route Not Found</Badge>
          <h1 className="text-2xl font-semibold text-slate-900 tracking-tight">
            Page does not exist
          </h1>
          <p className="text-xs text-slate-500 leading-relaxed">
            No route matched <code className="font-mono text-slate-700 bg-slate-100 px-1.5 py-0.5 rounded">{location.pathname}</code>.
          </p>
          <div className="flex items-center justify-center gap-2 pt-2">
            <Button variant="primary" onClick={() => navigate('/')}>
              Back to Overview
            </Button>
            <Button variant="secondary" onClick={() => navigate('/lab')}>
              Open SMILES Interpreter
            </Button>
          </div>
        </div>
      </Card>
    </div>
  )
}
