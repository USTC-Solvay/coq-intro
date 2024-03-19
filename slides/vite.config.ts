import { defineConfig } from 'vite'
import lz from 'lz-string'

export default defineConfig({
  plugins: [
    {
      name: 'coq-editor',
      enforce: 'pre',
      transform: {
        order: 'pre',
        handler(code, id) {
          if (id.endsWith('.md')) {
            return code.replace(/^```coq editor\n([\s\S]*?)\n```/mg, (match, coqCode) => {
              return `<coq-editor code="${lz.compressToBase64(coqCode)}" />`
            })
          }
        }
      }
    },
  ]
})
