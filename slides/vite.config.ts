import { defineConfig } from "vite";
import lz from "lz-string";
import process from "process";

export default defineConfig(({ command }) => ({
  plugins: [
    {
      name: "coq-editor",
      enforce: "pre",
      transform: {
        order: "pre",
        handler(code, id) {
          if (id.endsWith(".md")) {
            return code.replace(
              /^```coq editor\n([\s\S]*?)\n```/gm,
              (match, coqCode) => {
                return process.env.EXPORT_SLIDES || command === 'build'
                  ? `\`\`\`coq\n${coqCode}\n\`\`\``
                  : `<coq-editor code="${lz.compressToBase64(coqCode)}" />`;
              },
            );
          }
        },
      },
    },
  ],
}));
