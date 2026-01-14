import esbuild from "esbuild";

const watch = process.argv.includes("--watch");

const ctx = await esbuild.context({
  entryPoints: ["index.ts"],
  bundle: true,
  format: "iife",
  target: ["es2019"],
  outfile: "dist/proofnav.bundle.js",
  sourcemap: true,
  minify: true
});

if (watch) {
  await ctx.watch();
  console.log("proofnav: watching...");
} else {
  await ctx.rebuild();
  await ctx.dispose();
  console.log("proofnav: built");
}
