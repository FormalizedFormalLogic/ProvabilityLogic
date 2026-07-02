# move-gentzen-fixedpoint-to-logic-gl

## タスク内容

`SeqPL/Gentzen/Fixedpoint.lean`（GL の不動点定理，SV82 Section 4 の形式化）は，
Gentzen 体系そのものというより GL という論理に関する内容なので，
`SeqPL/Logic/GL/` 配下へ移動する．

## 方針

- `git mv SeqPL/Gentzen/Fixedpoint.lean SeqPL/Logic/GL/Fixedpoint.lean`
- `SeqPL.lean` の import 行を更新（`SeqPL.Gentzen.Fixedpoint` → `SeqPL.Logic.GL.Fixedpoint`），
  import順もアルファベット順を保つよう Logic.GL セクションへ移す．
- 他に `SeqPL.Gentzen.Fixedpoint` を import しているファイルは無いことを確認済み（grep 済み）．
- ファイル内の import 文自体は相対パスではなくフルパス（`SeqPL.Gentzen.Maehara` 等）なので，
  移動後もそのまま有効なはず．中身のコード変更は不要な想定．
- 移動後 `lake build SeqPL.Logic.GL.Fixedpoint` で通ることを確認．
- 最後に `lake exe mk_all --module` で `SeqPL.lean` を更新．

## 現状

- worktree 作成，.lake ハードリンク複製済み．
- `git mv SeqPL/Gentzen/Fixedpoint.lean SeqPL/Logic/GL/Fixedpoint.lean` 実施済み．
- `SeqPL.lean` の import を修正し，`lake exe mk_all --module` が「No update necessary」となることを確認．
- `lake build SeqPL` で 1253/1253 成功（残存 sorry は本作業と無関係の既存箇所のみ）．
- コミット・報告待ち．
