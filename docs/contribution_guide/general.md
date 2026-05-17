# General guideline

We're currently allowing PRs in 4 flavors. They come with a fixed naming on titles: `Author@what-you-have-done`:

- Formal proofs for a chapter, titled with `Author@Proofs for chapter x, part y`. The parts are expected to be specified by some issue in the issue list when we're focusing on that part of proof. The corresponded branch name is strictly required to be `author@chxx-proof-y`
- Documentation update, titled with `Author@Documentation update mmddyyyy`. You should push with a branch naming as `author@documentationmmddyyyy`
- Any other kind of features, for example, setting up CI, adding more automation or external supports, should be titled with `Author@Miscellaneous maintainence mmddyyyy`. The branch name is `author@miscmmddyyyy`.
- If you have only implemented a single misc feature, you can name as whatever you want: `Author@what-you-have-done`. The branched name is `author@what-have-you-done`.

For all these PR: please list what you have done in the description.

For PRs involving coding: please make sure...
- Your branch has passed through the GitHub Workflow.
- You code style matches up with what have been specified in our documentation.
- Your code's namings are sticking to our style guide as close as possible.
