# Release procedure

## Preparation

A few days before: write a post on blog.spade-lang.org highlighting important changes. Possibly also
take the opportunity to highlight other stuff that normally doesn't fit in a blog post, like new projects, publications? etc.

## Pre release procedure

- [x] Spade
    - [x] Update changelog
        - [x] Bump [unreleased] to [x.y.z].
        - [x] Update unreleased compare link to latest version
        - [x] Make sure the version header links to the diff between this and the previous version
    - [x] Bump cargo.toml version
- [x] Swim
    - [x] Update changelog
        - [x] Bump [unreleased] to [x.y.z].
        - [x] Make sure the version header links to the diff between this and the previous version
    - [x] Bump cargo.toml version

## Release

- [x] Merge changelog update MRs
    - [x] Spade
    - [x] Swim
- [x] Tag resulting commit as `vX.Y.Z`
    - [x] Spade
    - [x] Swim
- [x] Push tags
    - [x] Spade
    - [x] Swim
- [ ] Do a release on gitlab
- [ ] Upload Spade release to zenodo
- [ ] Update release blog post MR with link to relevant changelog section. Merge blog

## Post release

- [ ] Announcements
    - [ ] Discord
    - [ ] Mastodon
    - [ ] Twitter

