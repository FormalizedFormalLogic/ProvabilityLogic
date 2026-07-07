# SeqPL プロジェクト指示

## 環境セットアップ（plugin と MCP）

このプロジェクトでは Lean の証明作業に **`lean4-skills` plugin** と **`lean-lsp` MCP** を使う．新規にクローンした際は以下を有効化すること．リポジトリには `.claude/settings.json`（marketplace 登録）と `.mcp.json`（MCP server 定義）をコミット済みなので，Claude Code がクローン後にこれらの追加をサジェストする．

- **`lean4` plugin（marketplace `lean4-skills`）**: `.claude/settings.json` の `extraKnownMarketplaces` に marketplace `lean4-skills`（GitHub `cameronfreer/lean4-skills`）を登録済み．クローン後に marketplace 追加がサジェストされるので承認し，plugin 本体は明示的に導入する．
  ```
  /plugin marketplace add cameronfreer/lean4-skills   # settings.json 済みなら自動サジェスト
  /plugin install lean4@lean4-skills
  ```
  これにより `/lean4:autoprove` をはじめとする証明支援コマンドが使えるようになる．
- **`lean-lsp` MCP server**: `.mcp.json` に `uvx lean-lsp-mcp`（stdio）を定義済み．クローン後にプロジェクトを開くと承認プロンプトが出るので許可する．LSP による高速な対話的証明フィードバック（`mcp__lean-lsp__lean_goal` 等）を提供する．
  - 前提: `uvx`（uv）と `ripgrep`（`rg`）がインストールされていること．

## Lean の証明作業のワークフロー

sorry を埋める，補題を証明する，リファクタするなど Lean の証明作業を行うときは，以下に従う．

- **必ず worktree を切って作業する**．`main` で直接作業しない．ブランチを切るだけで worktree を作らない，というのも不可．worktree はリポジトリ直下の `.claude/worktrees/<branch>` に作成する（`.claude/worktrees/` は `.git/info/exclude` で除外済み）．`gwq` は `EnterWorktree` 等のツールと管理パスが競合するため使わない．
- **`main` ブランチ（メインリポジトリの worktree）上での直接のファイル変更は原則禁止**．例外は，ユーザーからの明示的な指示に基づき `CLAUDE.md` または `.gitignore` を変更する場合のみで，それ以外のファイルおよびそれ以外の状況（明示的指示がない場合）では，Claude やサブエージェントが `main` 上でファイルを変更してはならない．`main` での作業指示を受けたときも，上記の例外に該当しない限り必ず新しい worktree を作成してそこで作業する．なお，この禁止は `git status`・`git diff` 等の直接のファイル編集を伴わない操作や，ユーザー承認後に作業ブランチを `main` へ squash マージする操作（下記の「勝手にマージしない」の項目に従う）には適用されない．
  ```
  git worktree add .claude/worktrees/<branch> -b <branch>
  ```
- **worktree 作成後，必ずプロジェクトルートの `.lake` を worktree へコピーする**（`cp -al` でハードリンク複製する）．コピーしないと Mathlib と FFL のビルドに凄まじい時間がかかってしまう．
- **証明には `/lean4:autoprove` スキルを使う**．sorry を埋める・補題を証明する際は autoprove で進める．
- **タスクの種類に応じてサブエージェントのモデルを使い分ける**．
  - **より難易度の高い形式証明（新規の sorry 埋め・補題証明など）には Fable を使う**．サブエージェントを起動する際も `model: fable` を指定する．
  - **形式証明のリファクタリング（既存証明の整理・補題の分割・命名の整理など）には Opus を使う**．Sonnet ではリファクタリングの質が不十分だったため，`model: opus` を指定する．
  - **それ以外の日常的なタスク**（`Foundation` など他のコードを参考として調べる，論文 PDF をスキャンするといった軽い調査作業）**には低コストのモデル（Sonnet・Haiku）を使う**．
- **Fable をモデルとするサブエージェントを起動する際は，auto-edit（自動承認）モードであっても必ず事前にユーザーの承認を取る**．コストの高いモデルであるため，起動前に対象タスク・見積もりを提示し，ユーザーが明示的に許可してから起動すること．
- **一つの補題（sorry）を埋める度にコミットする**．まとめて一度にコミットしない．
- **全ての作業が完了しても，勝手に `main` へマージしない**．ブランチ名・変更内容・ビルド確認結果を報告し，ユーザーの確認を待つ．承認されたら `main` に squash マージし，マージ後は作業ブランチを削除する．
- コミット・マージの前に該当モジュールが `lake build` で通ること，および LSP 診断にエラー・警告（残存 sorry を含む）が無いことを確認する．
- **worktree での作業を終える際は，必ず `lake exe mk_all --module` を実行して `SeqPL.lean` を更新する**．新しいファイルを追加した場合の import 漏れを防ぐため．これは今後ユーザーの許可なく実行してよい．
- **worktree に入る際は `EnterWorktree` ツールを `path` 引数付きで呼び，セッションの作業ディレクトリ自体を切り替える**．`git worktree add .claude/worktrees/<branch> -b <branch>` でブランチと worktree を作成し `.lake` をハードリンク複製した後，`$(git rev-parse --show-toplevel)/.claude/worktrees/<branch>` の絶対パスを `EnterWorktree` の `path` に渡す．これにより以降のツール呼び出しで毎回 `cd` を書く必要がなくなる．`EnterWorktree` の `name` 引数（新規 worktree 自動作成）は `.lake` 複製手順を経ないため使わない．作業終了時は `ExitWorktree` を `action: "keep"` で呼んで元のディレクトリへ戻る．
- **worktree や main のパスが必要な場面では，`git worktree list` または `$(git rev-parse --show-toplevel)/.claude/worktrees/<branch>` から取得する**．`~/ghq/...` のような絶対パスを手で組み立てたり `gwq` に頼ったりしない．`.lake` の複製先・`.claude/directions` の参照先・`EnterWorktree` の `path` など，パスを扱う全ての場面に適用する．

### worktree での作業と `.claude/directions/` による進捗共有

`.claude/directions/` は git 管理対象外（`.git/info/exclude` 済み）のディレクトリであり，異なるセッション・エージェント間の進捗共有に使う．worktree はメインリポジトリ直下の `.claude/worktrees/<branch>` に作られるため，worktree 側にコピーしたりシンボリックリンクを貼ったりする必要はなく，**メインリポジトリルート（`main` の worktree）の `.claude/directions/` を worktree から直接パス指定で読み書きする**．メインリポジトリルートは `$(dirname $(git rev-parse --git-common-dir))` で取得できる（worktree 内でも常にメインリポジトリの `.git` を指す）．

- **ユーザーから指示を受けたら，必ず新しい worktree を作って作業を始める**（Lean の証明作業に限らず，リファクタ・ドキュメント修正など全ての作業に適用する）．タスク内容を表す適当な slug（kebab-case）を決めてブランチ・worktree を作成する．
- **worktree を作成したら，実際の作業（証明・編集など）に着手する前に，必ず最初に以下の2つを行う**．いずれもメインリポジトリルートの `.claude/directions/` を直接編集する（例: `$(dirname $(git rev-parse --git-common-dir))/.claude/directions/{{slug}}.md`）．
  1. **`.claude/directions/worktrees.md` にチェックボックスのリストアイテムを追加する**．slug と何をするかを端的に書く（例: `- [ ] my-slug — ○○の証明`）．作業が完了したらチェックを入れる．
  2. **`.claude/directions/{{slug}}.md` を作成し，このworktreeで何をするか（タスク内容・方針・現状）を書き込む**．
- **`.claude/directions/{{slug}}.md` は基本的に 1 コミットごとに更新し，他のセッションやエージェントが `.claude/directions/worktrees.md` を見れば状況を把握して共同作業できる状態を保つ**．メインリポジトリの実体を直接編集するため，マージ完了を待たずに他の worktree からも即座に見える．

## 言語について

- ユーザーとの応答（チャット・報告など）は引き続き日本語で書く．
- **git のコミットメッセージは必ず英語で書く**．件名・本文・`Co-Authored-By` などの trailer を含め全て英語にする．

## 参考実装

- 証明の方針に迷ったら，依存先の `Foundation`（`.lake/packages/Foundation/`）の対応する補題の証明を参考にする．
- `Foundation` の Vorspiel にある補題で SeqPL に無いものは，必要に応じて `SeqPL/Vorspiel/` に移植してよい．

## 参考文献 PDF（`.notes/`）と `references.bib`

- `.notes/`（git 管理対象外）には，形式化の元になる論文の PDF を置く．ファイル名は `references.bib` の BibTeX キーに合わせる（例: `Bek90.pdf` は `references.bib` の `Bek90` エントリに対応）．新しい論文 PDF を追加したときは，対応する `references.bib` エントリも追加し，ファイル名をそのキーにリネームする．
- 未出版・非公式な資料（自分用ノート，ブログ記事，リポジトリ上のメモなど，正式な参考文献にならないもの）は `.notes/unpublished/` に置き，`references.bib` には載せない．
- 参考文献のメタデータ・BibTeX の取得には Zotero MCP（`mcp__zotero__*` ツール，ユーザースコープで設定済み）を使う．
- `references.bib` は `.bibtoolrsc`（`Foundation` から移植，SeqPL 用に一部カスタマイズ済み）で整形・キー生成する．新しいエントリを追加した，または既存エントリを直した後は必ず以下を実行する．
  ```
  just format-bib
  ```
- BibTeX キーの命名規則は AMS（MathSciNet/MRef）方式に準拠する（例: `Bek90`，`AB05`，`JdJ98` の `de Jongh` の `d`）．具体的なフォーマットは `.bibtoolrsc` の `key.format`・`fmt.name.name`・`new.format.type {2 = ...}` の設定に委ねており，人手でキーを整えず `just format-bib` の出力に従う．
- キーを生成し直したら，対応する `.notes/` 内の PDF ファイル名も新しいキーに合わせてリネームすること．

## 形式証明を書くにあたって

### docstring と証明中のコメント

- コード中のコメント（Lean のドキュメントコメント `/-- -/` やインラインコメントなど）は英語で書く．
- **各定理・補題の docstring には，statement の簡単な説明だけを載せればよく，証明の方針まで書く必要はない**．
- 証明の方針は基本的にそれほど書く必要はないが，**他の証明のために残しておいたほうがよいと判断した場合にのみ**，証明の中にスケッチとして書いておくか，各証明行の必要な部分にコメントとして書く．

### インデント

宣言シグネチャが複数行にわたるときは，インデントを次のように整えること．

- **シグネチャの第1レベルの継続行は，宣言キーワード（`lemma`/`theorem`/`def` など）から 2 スペース（1 レベル）だけ下げる**．該当するのは以下:
  - `:` の後ろの型を `↔`・`→` などで折り返した各行
  - binder を各行に分けて書くときの各 binder 行（`(h : ...)` など）
  - 返り値を独立行に置くときの `: ...` 行
- **Lean のデフォルトのような 4 スペースにしたり，行が下がるごとに段々深くする階段状インデントにしたりしない**．
- 例外は「1 つの binder（や返り値の型）自体が長くて折り返す場合」だけで，そのときはその binder の内側の継続をさらに 1 レベル（合計 4 スペース）下げてよい（下の良い例の 2 つ目 `(hindep : ...)` を参照）．

悪い例（4 スペース・階段状で深すぎる）:

```
lemma forces_root_modalized_o_indep {A : Formula α} (hA : A.Modalized) :
    Forces (M := (M.toPseudoTail r o).toModel) (toPseudoTail.chainPoint ⊤) A ↔
      Forces (M := (M.toPseudoTail r o').toModel) (toPseudoTail.chainPoint ⊤) A := by

lemma exists_modalized_equiv_of_indep
    (hindep : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL]
        (r : M.World) (o o' : α → Prop),
      (M.toPseudoTail r o).root.1 ⊩ C ↔
        (M.toPseudoTail r o').root.1 ⊩ C) :
    ∃ C', C'.Modalized ∧ (C 🡘 C') ∈ LogicD ∧ C'.atoms ⊆ C.atoms := by
```

良い例（第1レベルは 2 スペース，長い binder の内側だけ 4 スペース）:

```
lemma forces_root_modalized_o_indep {A : Formula α} (hA : A.Modalized) :
  Forces (M := (M.toPseudoTail r o).toModel) (toPseudoTail.chainPoint ⊤) A ↔
  Forces (M := (M.toPseudoTail r o').toModel) (toPseudoTail.chainPoint ⊤) A := by

lemma exists_modalized_equiv_of_indep
  (hindep :
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL] (r : M.World) (o o' : α → Prop),
    (M.toPseudoTail r o).root.1 ⊩ C ↔ (M.toPseudoTail r o').root.1 ⊩ C
  )
  : ∃ C', C'.Modalized ∧ (C 🡘 C') ∈ LogicD ∧ C'.atoms ⊆ C.atoms := by
```

### `grind` タクティクについて

各補題や定義について積極的に `@[grind]` 属性を付けていくこと．`@[grind =>]` などどのような方向にするかは任せる．
証明の中でも積極的に `grind` を使うことを試して，なるべく証明を簡略化すること．

### 実装の作法

可読性のために記法としては以下を守ってください．

- 各証明の1行毎に適当にセミコロン(`;`)を必ず入れること．
- 証明の各主張で implicit variables を一々定義するのはできるだけ避けて，`variables` で共通化することを心がけてください．
- `∃ a, ...` 系のgoalを示す際は，`refine` ではなくて `use` をなるべく使ってほしい．`?_` の使用はなるべく避けてほしい．
  - ただし複数のpropositionの連言で `refine ⟨?_, ⟨?_, ?_⟩, ?_⟩` のようにするのは良い．この場合は `constructor` などで対処しないこと．
  - ただし `refine ⟨?_, ?_⟩`（プレースホルダが2つだけの単純な2分割）に限っては，`constructor` を使ってよい．
- `universe u` などの宣言は必要無ければしなくても良い．

数学的・論理学的な注意としては以下を守ってください．

- モデルのworldで `κ : Type u` を使うことが多いが，他のモデルから別のモデルを作るとき，`κ` を使わずに `Model.World` を使いなさい．
- 命名は以下の規則を必ず守ること・
  - Kripkeモデルについて
    - Worldは `x, y, z, w, v, u` などを使え．
  - 様相論理について：
    - 命題変数については `a`, `b`, `c` などの最初の方の小文字のアルファベットを使う．
      - なるべく証明に現れる論理式は `A, B, C, D` のように順番に現れるように．`A, B, E` のようにスキップして現れるのは避けること．
    - 論理式には `A`, `B`, `C` などの最初のほうのLatinの大文字のアルファベットを使う．
      - 特に，`φ`, `ψ`といったギリシャ文字や，`P, Q, X, Y` などの後半のアルファベットは，意図が被ってしまうので決して使わない．
    - 論理式のリストまたは有限集合には `Γ`, `Δ` を使う．
    - 論理式の集合には `X`, `Y`, `Z` を使う．
  - 1階述語論理について
    - 論理式には `φ`, `ψ`，`χ` などのギリシャ文字を使う．
    - 閉論理式には `σ`，`π` などのギリシャ文字を使う．
- 最終的に論理の特徴を `provability_TFAE` で証明するパターンが多いが，他の証明で例えば `provability_TFAE.out 1 0` を使うのは出来るだけやめて，適宜補題としてきりだしておいてください．
  - TFAEのインデックスが変わる場合があるので．
- 可読性を上げるために，論理について，型推論を行うときは，`@LogicGL α` のような記法を積極的に使って，論理式に型注釈を与える（`A : Formula α`）のを避けてください．

### Tips

- 特に論理式の構成で `induction` を回す際，`bot` と `imp` に関しては `grind` や `simp_all` などで自明に証明出来る場合が多い．とりあえず試してみること．
