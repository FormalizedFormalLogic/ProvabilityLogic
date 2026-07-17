# Lean プロジェクト指示

## セットアップ

このプロジェクトでは Lean の証明作業に **`lean4-skills` plugin** と **`lean-lsp` MCP** を使う．新規にクローンした際は以下を有効化すること．リポジトリには `.claude/settings.json`（marketplace 登録）と `.mcp.json`（MCP server 定義）をコミット済みなので，Claude Code がクローン後にこれらの追加をサジェストする．

- **`lean4` plugin（marketplace `lean4-skills`）**: `.claude/settings.json` の `extraKnownMarketplaces` に marketplace `lean4-skills`（GitHub `cameronfreer/lean4-skills`）を登録済み．クローン後に marketplace 追加がサジェストされるので承認し，plugin 本体は明示的に導入する．
  ```
  /plugin marketplace add cameronfreer/lean4-skills   # settings.json 済みなら自動サジェスト
  /plugin install lean4@lean4-skills
  ```
  これにより `/lean4:autoprove` をはじめとする証明支援コマンドが使えるようになる．
- **`lean-lsp` MCP server**: `.mcp.json` に `uvx lean-lsp-mcp`（stdio）を定義済み．クローン後にプロジェクトを開くと承認プロンプトが出るので許可する．LSP による高速な対話的証明フィードバック（`mcp__lean-lsp__lean_goal` 等）を提供する．
  - 前提: `uvx`（uv）と `ripgrep`（`rg`）がインストールされていること．
- 参考文献のメタデータ・BibTeX の取得には Zotero MCP（`mcp__zotero__*` ツール，ユーザースコープで設定済み）を使う．

## ワークフロー

### worktree での作業

Lean の証明作業（sorry を埋める，補題を証明する，リファクタする）に限らず，ユーザーから指示を受けた作業は原則すべて worktree を切って行う．

- **必ず worktree を切って作業する**．`main` で直接作業しない．ブランチを切るだけで worktree を作らない，というのも不可．worktree はリポジトリ直下の `.claude/worktrees/<branch>` に作成する（`EnterWorktree` ツールがこのパス配下の worktree にしか対応していないため）．`.claude/worktrees/` は `.git/info/exclude` で除外済み．`gwq` は `EnterWorktree` 等のツールと管理パスが競合するため使わない．
  ```
  git worktree add .claude/worktrees/<branch> -b <branch>
  ```
- **`main` 上での直接のファイル変更は原則禁止**．例外は，ユーザーからの明示的な指示に基づき `CLAUDE.md` または `.gitignore` を変更する場合，および `references.bib` への文献追加・修正（対応する `.notes/` の PDF リネームや `just format-bib` の実行を含む）を行う場合のみ．`main` での作業指示を受けたときも，上記の例外に該当しない限り必ず新しい worktree を作成する．この禁止は `git status`・`git diff` 等の非破壊操作，およびユーザー承認後の squash マージ操作には適用されない．
- **worktree 作成後，必ずプロジェクトルートの `.lake` を worktree へコピーする**（`cp -al` でハードリンク複製する）．コピーしないと Mathlib 等の依存パッケージのビルドに凄まじい時間がかかる．
- **worktree に入る際は `EnterWorktree` ツールを `path` 引数付きで呼ぶ**．`$(git rev-parse --show-toplevel)/.claude/worktrees/<branch>` の絶対パスを渡すことで，以降のツール呼び出しで毎回 `cd` を書く必要がなくなる．`EnterWorktree` の `name` 引数（新規 worktree 自動作成）は `.lake` 複製手順を経ないため使わない．作業終了時は `ExitWorktree` を `action: "keep"` で呼んで元のディレクトリへ戻る．
- **worktree や main のパスが必要な場面では，`git worktree list` または `$(git rev-parse --show-toplevel)/.claude/worktrees/<branch>` から取得する**．

### `.directions/` による進捗共有

`.directions/` は git 管理対象外のディレクトリで，異なるセッション・エージェント間の進捗共有に使う．worktree はメインリポジトリ直下の `.claude/worktrees/<branch>` に作られるため，メインリポジトリルート（`$(dirname $(git rev-parse --git-common-dir))`）の `.directions/` を worktree から直接パス指定で読み書きする．

- worktree を作成したら，実際の作業に着手する前に必ず以下の 2 つを行う．
  1. `.directions/worktrees.md` にチェックボックスのリストアイテムを追加する（例: `- [ ] my-slug — ○○の証明`）．完了したらチェックを入れる．
  2. `.directions/{{slug}}.md` を作成し，このworktreeで何をするか（タスク内容・方針・現状）を書き込む．ファイル名には作成時刻を分刻みで表す `YYYYMMDDHHMM_` prefix を付ける（例: `YYYYMMDDHHMM_<slug>.md`）．`worktrees.md` 自体には prefix を付けない．
- `.directions/{{slug}}.md` は基本的に 1 コミットごとに更新し，他のセッション・エージェントが `worktrees.md` を見れば状況を把握できる状態を保つ．
- **`.directions/` およびその配下のファイルは，いかなる理由があっても削除してはならない**．git 管理対象外であるため誤って削除すると復元できず，他のセッション・エージェントとの進捗共有が失われる．完了したタスクの記録であっても，ユーザーから明示的に削除の指示を受けた場合を除き，`.directions/{{slug}}.md` や `.directions/worktrees.md` のエントリを削除・整理してはならない．完了した記録は削除せず，`.directions/worktrees.md` 上でチェックを入れる・完了セクションへ移すなどの方法で残すこと．worktree 整理（`git worktree remove` など）を行う際も，`.directions/` 配下のファイルには手を触れない．

### サブエージェントとモデルの使い分け（Lean 証明作業）

- **紙とペンによる証明のプラン立案には必ず Fable を使う**．新規の sorry 埋め・補題証明に着手する前に，まず Fable のサブエージェント（`model: fable`）に証明の方針を立案させる．Fable には Lean コードを書かせず，あくまで数学的な証明のプランニングのみを担当させる．
  - Fable の起動は auto-edit（自動承認）モードであっても必ず事前にユーザーの承認を取る．起動前に対象タスク（プラン立案の範囲）・見積もりを提示し，ユーザーが明示的に許可してから起動する．
- **Fable が立案したプランは，必ず統合するために作ったメインのブランチ（並列化した worktree を統合する先のブランチ）に，全ての詳細を記載する**．ユーザーが大まかな内容を確認できるように，かつセッションが切れた場合でもそのブランチの内容から作業を復帰できるように，ステップの分割前の元のプランと，分割後の各ステップの内容を省略せずファイルとしてコミットしておく．並列化のために複数の worktree に分岐した場合も，各ステップの割り当て先（どの worktree/ブランチが担当するか）を統合用ブランチ側のこのファイルに追記して一覧できるようにする．**プランを後から修正・再立案した場合も上書きせず追記し，変更履歴が残るようにする**．
- **Fable が立案したプランは，必ず適当な複数の細かいステップに分割させる**．補題として切り出せる中間ステップ・場合分けの各ケースなど，扱いやすい単位に分ける．並列化しやすい粒度・ファイル分割を意識させる．
- **形式証明を書く際は，まず骨組みを作ってから中身を埋める順序を守る**．
  1. プランに登場する補題すべてを，中身は `sorry` のまま主張（statement）だけ形式化する．
  2. 次に主定理を，それら sorry 化された補題を用いて形式化する（主定理の証明自体も sorry で残してよい）．
  3. 最後に，各補題の sorry を一つずつ埋めていく．
- **実装（Lean コードとして形式証明を書く部分）・リファクタリングは，可能な限り安価なモデルに任せる**．大抵は Sonnet で十分．Sonnet では通らない・質が不十分な場合に限り Opus を使う（`model: opus`）．
- **コーディネータ（メインループ）自身は，どれほど自明に見える内容であっても Lean の証明コードを直接書いてはならない**．必ずサブエージェントに外注する．
- **形式証明を書く際は，プランの細かいステップごとにサブエージェントを起動する**．1 ステップ = 1 エージェント呼び出しとし，ステップ完了ごとに進捗を報告する．**sorry を埋める・補題を証明するステップを委任する際は，起動するサブエージェントに `/lean4:autoprove` の利用を明示的に指示する．**
- **依存関係があっても，前段の補題を `sorry` で仮置きすれば worktree を並列化してよい**．
  1. 各補題の主張だけ先に確定させる．
  2. ファイルが分かれる（または明確に分離できる）ステップ群ごとに `git worktree add` で分岐し `.lake` を複製する．
  3. 各 worktree に専用ファイルを割り当てて並列にサブエージェントへ委任する．
  4. 完了したブランチを統合し，`sorry` を実際の証明に置き換えて `lake build` で確認する．
  - **並列化はできるだけ積極的に行う．可能なら補題1つあたりに1つの worktree を割り当てる**．「グループでまとめて1 worktree」ではなく「補題ごとに worktree を切る」方向を既定とし，ファイル競合を避けるため別ファイル（または明確に分離したセクション）に割り当てる．
  - **並列化する際は，統合用の worktree を1つ立てる**．ユーザーから最初に指示を受けて作成した作業用 worktree（タスクの slug に対応するブランチ）をそのまま統合先として使ってよく，別途新たな統合用ブランチを追加で切る必要はない．各補題用の worktree での作業が完了したら，都度この統合用 worktree に `git merge`（または該当ブランチの cherry-pick）で取り込み，`sorry` を実際の証明に置き換えて `lake build` で確認する．**マージや PR はこの統合用 worktree のブランチのみを対象とし**，個々の補題用 worktree のブランチを直接マージ・PR に出さない．統合が終わった補題用 worktree は不要になるので，`git worktree remove` とブランチ削除で片付ける．
- **それ以外の日常的なタスク**（依存先の他のコードを参考として調べる，論文 PDF をスキャンするといった軽い調査作業）**には低コストのモデル（Sonnet・Haiku）を使う**．
- **既存 docstring 群の一括リファクタリング**（証明コードは変更せずコメントのみを直す作業）は，Haiku のサブエージェントを多数並列起動して片付ける．ファイル単位（または小さいファイル群単位）で `model: haiku` を指定する．証明コードそのものを書く・直すタスクにはこの方針を適用しない．

### 証明の進め方・コミット・マージ

- **証明には `/lean4:autoprove` スキルを使う**．sorry を埋める・補題を証明する際は autoprove で進める．
- **一つの補題（sorry）を埋める度にコミットする**．まとめて一度にコミットしない．
- コミット・マージの前に該当モジュールが `lake build` で通ること，および LSP 診断にエラー・警告（残存 sorry を含む）が無いことを確認する．
- **全ての作業が完了しても，勝手に `main` へマージしない**．ブランチ名・変更内容・ビルド確認結果を報告し，ユーザーの確認を待つ．承認されたら `main` に squash マージし，作業ブランチを削除する．
- **worktree での作業を終える際は，必ず以下の順序で実行する**（今後ユーザーの許可なく実行してよい）．
  1. `lake build` で通ることを確認する．
  2. `just mk-all` を実行して all-import ファイルを更新する（新しいファイルを追加した場合の import 漏れを防ぐため．Justfile にターゲットが無ければ `lake exe mk_all` 等の相当コマンドを実行する）．
  3. `just shake` を実行して未使用 import・不要な `public` を除去する．`lake shake` は直前のビルドが完了していないと実行できないため，必ずビルド後に行う．
  4. shake が import を書き換えるため，もう一度 `lake build` を実行して通ることを確認する．
     - `lake shake --fix` は `native_decide` などの `meta` 定義に必要な `meta import` 行を，同じモジュールへの `public import` と重複していると誤認して削除し，ビルドを壊すことがある．**`meta import` 行を書く・見つけたときは，必ず行末に `-- shake: keep` アノテーションを付けて除外する**（例: `meta import <Module> -- shake: keep`）．ビルド失敗時は `Invalid \`meta\` definition ... is not accessible here; consider adding \`public meta import ...\`` のエラーを手がかりに，削除された行を復元し `-- shake: keep` を付けて再確認する．
  - **1つの論理的な作業を複数の worktree に分けて並列化している場合，この shake ステップは各 worktree で個別に実行する必要はない**．`lake shake` は全体ビルドが green であることを前提にしているため，統合先へマージし終えた後，統合先で一度だけ `just mk-all` → `just shake` → `lake build` を実行すれば十分．

### 言語について

- ユーザーとの応答（チャット・報告など）は日本語で書く．
- **git のコミットメッセージは必ず英語で書く**．件名・本文・`Co-Authored-By` などの trailer を含め全て英語にする．

### 参考文献 PDF（`.notes/`）と `references.bib`

- `.notes/`（git 管理対象外）には，形式化の元になる論文の PDF を置く．ファイル名は `references.bib` の BibTeX キーに合わせる（例: `<key>.pdf` は `<key>` エントリに対応）．新しい論文 PDF を追加したときは，対応する `references.bib` エントリも追加し，ファイル名をそのキーにリネームする．
- 未出版・非公式な資料（自分用ノート，ブログ記事，リポジトリ上のメモなど）は `.notes/unpublished/` に置き，`references.bib` には載せない．
- `references.bib` は `.bibtoolrsc` で整形・キー生成する．新しいエントリを追加した，または既存エントリを直した後は必ず以下を実行する．
  ```
  just format-bib
  ```
- BibTeX キーの命名規則は AMS（MathSciNet/MRef）方式に準拠する（例: `Bek90`，`AB05`，`JdJ98` の `de Jongh` の `d`）．具体的なフォーマットは `.bibtoolrsc` の `key.format`・`fmt.name.name`・`new.format.type {2 = ...}` の設定に委ねており，人手でキーを整えず `just format-bib` の出力に従う．
- キーを生成し直したら，対応する `.notes/` 内の PDF ファイル名も新しいキーに合わせてリネームすること．

## コードの書き方

### docstring と証明中のコメント

- コード中のコメント（Lean のドキュメントコメント `/-- -/` やインラインコメントなど）は英語で書く．
- **各定理・補題の docstring には，statement の簡単な説明だけを載せればよく，証明の方針まで書く必要はない**．
- 証明の方針は基本的にそれほど書く必要はないが，**他の証明のために残しておいたほうがよいと判断した場合にのみ**，証明の中にスケッチとして書いておくか，各証明行の必要な部分にコメントとして書く．
- **`see plan Step4 §3 L4-1` や `issue #707, Step 3`，`Step 2` のような，プラン内の番号・GitHub issue番号・章番号・行ラベル（`L4-1`／`§2`など）に依存するコメント・docstringは，証明をコミット・PR として提出する際に全て削除する**．module docstring 内の "issue #707, Step N" のような表題や，「Step 2 が未完成でも～」のような他ファイルの実装段階に依存した説明も対象．プラン立案時・実装時の作業用メモとしてコードに残すのは構わないが，そのプランはプラン用ファイル（`.directions/{{slug}}.md` や統合用ブランチのプランファイル）にのみ保存される一時的な参照であり，レビューする第三者やプラン自体が更新・消失した後の読者には意味が通らない．コミット・マージ前の確認（`lake build`／sorry 確認）の際に，`grep -n "see plan\|issue #\|Step [0-9]\|§[0-9]\|L[0-9]-[0-9]"` 等でこの種のコメント・docstringが残っていないか必ず確認し，見つかれば削除するか，issue番号・ステップ番号を含まない自然な説明に書き換える．
- **論文側の記法は，このリポジトリの実装名にリネームして書く**（例外: その定義自身の docstring で別名の由来を説明する記述は，リネームせずそのまま残してよい）．慣用的な省略はリネーム不要．
- **文献引用は `references.bib` の BibTeX キーだけを角括弧で書き，著者名・年号・論文タイトル・掲載誌をべた書きしない**．年号や著者名を見つけたら `references.bib` を検索して対応するキーに置き換える（対応するエントリが無ければブラケットを付けずそのまま歴史的言及として残す）．
- **文献引用は，本文の地の文に埋め込まず，docstring 末尾にリスト形式（`- [キー, 種別 番号]` の1行，例: `- [Key, Corollary 42]`）でまとめる**．引用が1件だけでも必ずリスト化し，`**Corollary 41(i) in [Key]**:` のような太字プレフィックスや「番号 in [キー]」の語順は使わない．
  - **リストは「1つの文献（BibTeXキー）につき1行」とする**．同じキーから複数の定理・補題を引用する場合は，キーごとに行を分けず，1行の角括弧内にカンマ区切りで列挙する（例: `- [Key, Theorem 10, Theorem 11(b), Theorem 11(c)]`）．異なるキーは行を分ける．

### インデント

宣言シグネチャが複数行にわたるときは，インデントを次のように整えること．

- **シグネチャの第1レベルの継続行は，宣言キーワード（`lemma`/`theorem`/`def` など）から 2 スペース（1 レベル）だけ下げる**．該当するのは以下:
  - `:` の後ろの型を `↔`・`→` などで折り返した各行
  - binder を各行に分けて書くときの各 binder 行（`(h : ...)` など）
  - 返り値を独立行に置くときの `: ...` 行
- 例外は「1 つの binder（や返り値の型）自体が長くて折り返す場合」だけで，そのときはその binder の内側の継続をさらに 1 レベル（合計 4 スペース）下げてよい（下の良い例の 2 つ目 `(hindep : ...)` を参照）．

悪い例（4 スペース・階段状で深すぎる）:

```
lemma foo_bar_indep {A : Baz α} (hA : A.Cond) :
    P (f a b) A ↔
      P (f a' b) A := by

lemma exists_equiv_of_indep
    (hindep : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFoo]
        (r : M.World) (o o' : α → Prop),
      Q (M, r, o) ↔
        Q (M, r, o')) :
    ∃ C', Cond C' ∧ Rel C C' ∧ C'.small ⊆ C.small := by
```

良い例（第1レベルは 2 スペース，長い binder の内側だけ 4 スペース）:

```
lemma foo_bar_indep {A : Baz α} (hA : A.Cond) :
  P (f a b) A ↔
  P (f a' b) A := by

lemma exists_equiv_of_indep
  (hindep :
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFoo] (r : M.World) (o o' : α → Prop),
    Q (M, r, o) ↔ Q (M, r, o')
  )
  : ∃ C', Cond C' ∧ Rel C C' ∧ C'.small ⊆ C.small := by
```

### `grind` タクティクについて

各補題や定義について積極的に `@[grind]` 属性を付けていくこと．`@[grind =>]` などどのような方向にするかは任せる．
証明の中でも積極的に `grind` を使うことを試して，なるべく証明を簡略化すること．

### `set_option maxHeartbeats` について

- **証明を通すために `set_option maxHeartbeats` を変更するのはなるべく避けること**．heartbeats を伸ばして無理に通すのは，証明が非効率な形になっているサインであることが多い．
- 一旦 `set_option maxHeartbeats` を使って証明を通せた場合でも，そのままにせず，後でリファクタリングして `maxHeartbeats` の変更が不要な形の証明に直すこと（補題として切り出す，`grind`/`simp` の対象を絞る，計算量の大きい定義を避けるなど）．

### 実装の作法

可読性のために記法としては以下を守ってください．

- 各証明の1行毎に適当にセミコロン(`;`)を必ず入れること．
- 証明の各主張で implicit variables を一々定義するのはできるだけ避けて，`variables` で共通化することを心がけてください．
- `∃ a, ...` 系のgoalを示す際は，`refine` ではなくて `use` をなるべく使ってほしい．`?_` の使用はなるべく避けてほしい．
- 複数のpropositionの連言（`refine ⟨?_, ⟨?_, ?_⟩, ?_⟩` のようなネストしたAnd）は，`refine` や `constructor` ではなく，可能な限り `and_intros` を使って分解すること．
- `∃ a, ...` 系の仮定から値を取り出す際は，`rintro`・`rcases` ではなく，可能な限り `obtain` を使うこと．
- **`refine ⟨…, fun x hx => ?_⟩` のように，`refine`の中で束縛変数（`fun x hx => …`）を直接書いて`?_`に繋げるのは分かりづらいので避ける．代わりに`refine ⟨…, ?_⟩`として`?_`のまま残し，生成されたsubgoalの中で`intro x hx`を使うこと．**
- `universe u` などの宣言は必要無ければしなくても良い．
- `TFAE`（`List.TFAE` 等）で複数の同値性をまとめて証明するパターンを使う場合，他の証明で `foo_TFAE.out 1 0` のようにインデックス指定で参照するのはできるだけ避け，適宜補題として切り出しておく（TFAE のインデックスは並び順が変わると崩れるため）．

### Tips

- 帰納法（`induction`）を回す際，自明な場合分け（base case や単純な再帰ケースなど）は `grind` や `simp_all` で証明できることが多い．とりあえず試してみること．

### プロジェクト特有の作法

このプロジェクト（ProvabilityLogic）のドメイン（様相論理・証明論理・Kripke モデル）に固有の作法．
他プロジェクトに流用する際は，このセクションを対象プロジェクトのドメインに合わせて書き換えるか削除すること．

- **論文側の記法（例: `GLαω`）は，このリポジトリの実装名（例: `LogicA`）にリネームして書く**．対応表の主な例:
  - `GLαω` → `LogicA`，`GLα X` → `LogicGLAlpha X`，`GLβ⁻ X` → `LogicGLBetaMinus X`，`GLLin`/`GLlin`/`K4.3W` → `LogicGLPoint3`．
  - 例外: その定義自身の docstring で「also known as `GLLin` or `K4.3W` in Sambin & Valentini」のように別名の由来を説明する記述は，リネームせずそのまま残してよい．
  - `GL`・`D`・`S`・`A`・`TBB` のような慣用的な省略はリネーム不要．
- モデルのworldで `κ : Type u` を使うことが多いが，他のモデルから別のモデルを作るとき，`κ` を使わずに `Model.World` を使いなさい．
- 命名は以下の規則を必ず守ること．
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
    - 論理式(Formula)には `φ`, `ψ`，`χ` などのギリシャ文字を使う．
    - 閉論理式(Sentence)には `σ`，`π` などのギリシャ文字を使う．
- 最終的に論理の特徴を `provability_TFAE` で証明するパターンが多いが，他の証明で例えば `provability_TFAE.out 1 0` を使うのは出来るだけやめて，適宜補題としてきりだしておいてください．
  - TFAEのインデックスが変わる場合があるので．
- 可読性を上げるために，論理について，型推論を行うときは，`@LogicGL α` のような記法を積極的に使って，論理式に型注釈を与える（`A : Formula α`）のを避けてください．
