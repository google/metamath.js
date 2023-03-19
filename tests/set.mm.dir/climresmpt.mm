include "cli.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "reseq1i.mm"
include "a1i.mm"
include "wss.mm"
include "wcel.mm"
include "syl6eleq.mm"
include "uzss.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "resmpt.mm"
include "eqcomi.mm"
include "3eqtrrd.mm"
include "breq1d.mm"
include "cz.mm"
include "cvv.mm"
include "wb.mm"
include "eluzelz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "syl5eqel.mm"
include "climres.mm"
include "syl2anc.mm"
include "bitrd.mm"

theorem climresmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume climresmpt.z: |- Z = ( ZZ>= ` M )
  assume climresmpt.f: |- F = ( x e. Z |-> A )
  assume climresmpt.n: |- ( ph -> N e. Z )
  assume climresmpt.g: |- G = ( x e. ( ZZ>= ` N ) |-> A )

  disjoint N x
  disjoint Z x
  assert |- ( ph -> ( G ~~> B <-> F ~~> B ) )

  proof
    wph
    cG
    cB
    cli
    wbr
    cF
    cN
    cuz
    cfv
    #
    cres
    #
    cB
    cli
    wbr
    #
    cF
    cB
    cli
    wbr
    #
    wph
    cG
    @1
    cB
    cli
    wph
    @1
    vx
    cZ
    cA
    cmpt
    #
    @0
    cres
    #
    vx
    @0
    cA
    cmpt
    #
    cG
    @1
    @5
    wceq
    wph
    cF
    @4
    @0
    climresmpt.f
    reseq1i
    a1i
    wph
    @0
    cZ
    wss
    @5
    @6
    wceq
    wph
    @0
    cM
    cuz
    cfv
    #
    cZ
    wph
    cN
    @7
    wcel
    #
    @0
    @7
    wss
    wph
    cN
    cZ
    @7
    climresmpt.n
    climresmpt.z
    syl6eleq
    #
    cM
    cN
    uzss
    syl
    climresmpt.z
    syl6sseqr
    vx
    cZ
    @0
    cA
    resmpt
    syl
    @6
    cG
    wceq
    wph
    cG
    @6
    climresmpt.g
    eqcomi
    a1i
    3eqtrrd
    breq1d
    wph
    cN
    cz
    wcel
    #
    cF
    cvv
    wcel
    @2
    @3
    wb
    wph
    @8
    @10
    @9
    cM
    cN
    eluzelz
    syl
    wph
    cF
    @4
    cvv
    climresmpt.f
    @4
    cvv
    wcel
    wph
    vx
    cZ
    cA
    cZ
    @7
    cvv
    climresmpt.z
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    syl5eqel
    cB
    cF
    cN
    cvv
    climres
    syl2anc
    bitrd
end
