# Release procedure

## Preparation

A few days before: write a post on blog.spade-lang.org highlighting important changes. Possibly also
take the opportunity to highlight other stuff that normally doesn't fit in a blog post, like new projects, publications? etc.

## Pre release procedure

- [ ] Spade
    - [ ] Update changelog
        - [ ] Bump [unreleased] to [x.y.z].
        - [ ] Make sure the version header links to the diff between this and the previous version
- [ ] Swim
    - [ ] Update changelog
        - [ ] Bump [unreleased] to [x.y.z].
        - [ ] Make sure the version header links to the diff between this and the previous version

## Release

- [ ] Merge changelog update MRs
    - [ ] Spade
    - [ ] Swim
- [ ] Tag resulting commit as `vX.Y.Z`
    - [ ] Spade
    - [ ] Swim
- [ ] Push tags
    - [ ] Spade
    - [ ] Swim
- [ ] Do a release on gitlab
- [ ] Upload Spade release to zenodo
- [ ] Update release blog post MR with link to relevant changelog section. Merge blog

## Post release

- [ ] Announcements
    - [ ] Discord
    - [ ] Mastodon
    - [ ] Twitter
