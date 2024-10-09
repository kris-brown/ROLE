using Documenter
using Literate

const literate_dir = joinpath(@__DIR__, "literate")
const generated_dir = joinpath(@__DIR__, "src", "generated")

@info "Loading ROLE"
using ROLE

const no_literate = "--no-literate" in ARGS
if !no_literate
  @info "Building Literate.jl docs"

  # Set Literate.jl config if not being compiled on recognized service.
  config = Dict{String,String}()
  if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
    config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/kris-brown/ROLE.jl/blob/gh-pages/dev"
    config["repo_root_url"] = "https://github.com/kris-brown/ROLE.jl/blob/main/docs"
  end

  for (root, dirs, files) in walkdir(literate_dir)
    out_dir = joinpath(generated_dir, relpath(root, literate_dir))
    for file in files
      f, l = splitext(file)
      if l == ".jl" && !startswith(f, "_")
        Literate.markdown(joinpath(root, file), out_dir;
          config=config, documenter=true, credit=false, mdstrings=true)
        Literate.notebook(joinpath(root, file), out_dir;
          execute=true, documenter=true, credit=false, mdstrings=true)
      end
    end
  end
end

@info "Building Documenter.jl docs"
makedocs(
  modules=[ROLE],
  format=Documenter.HTML(
    size_threshold=600000000,    # in bytes
    size_threshold_warn=150000   # in bytes
  ),
  sitename="ROLE.jl",
  doctest=false,
  checkdocs=:none,
  warnonly=true,
  pages=Any[
    "ROLE.jl"=>"index.md",
    "Examples"=>Any[
      "generated/full_demo.md",
    ],
    "Library Reference"=>"api.md",
  ]
)

@info "Deploying docs"
deploydocs(
  target="build",
  repo="github.com/kris-brown/ROLE.jl.git",
  branch="gh-pages",
  devbranch="main"
)

@info "Done!"