{
  description = "The Olea programming language";

  inputs = {
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };
  outputs = {
    self,
    fenix,
    nixpkgs,
  }: let
    supportedSystems = nixpkgs.lib.systems.flakeExposed;
    allSystems = output:
      nixpkgs.lib.genAttrs supportedSystems
      (system: output nixpkgs.legacyPackages.${system});
  in {
    packages = allSystems (pkgs: {
      default = pkgs.rustPlatform.buildRustPackage {
        pname = "olea";
        version = "0.0.0";
        src = self;
        cargoLock.lockFile = ./Cargo.lock;
      };
    });

    devShells = allSystems (pkgs: let
      pkgsFenix = fenix.packages.${pkgs.system};
      # rust version 1.85
      rustPackages = pkgsFenix.beta.withComponents [
          "cargo"
          "clippy"
          "rustc" # includes rust-std
          "rustfmt"
          #"miri"
          #"rust-src" # rust stdlib source code. used by rust-analyzer and miri
        ];
    in {
      default = pkgs.mkShell {
        inherit
          (self.outputs.packages.${pkgs.system}.default)
          nativeBuildInputs
          buildInputs
          ;
        packages = [rustPackages];
        RUST_BACKTRACE = 1;
      };
    });
  };
}
