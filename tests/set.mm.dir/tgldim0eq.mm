include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "sylib.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "elsni.mm"
include "syl.mm"
include "eqtr4d.mm"
include "exlimddv.mm"

theorem tgldim0eq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cE: class E
  let cF: class F
  let vx: setvar x
  assume tgldim0.g: |- P = ( E ` F )
  assume tgldim0.p: |- ( ph -> ( # ` P ) = 1 )
  assume tgldim0.a: |- ( ph -> A e. P )
  assume tgldim0.b: |- ( ph -> B e. P )


  assert |- ( ph -> A = B )

  proof
    wph
    cP
    vx
    cv
    #
    csn
    #
    wceq
    #
    cA
    cB
    wceq
    vx
    wph
    cP
    chash
    cfv
    c1
    wceq
    #
    @2
    vx
    wex
    #
    tgldim0.p
    cP
    cvv
    wcel
    @3
    @4
    wb
    cP
    cF
    cE
    cfv
    cvv
    tgldim0.g
    cF
    cE
    fvex
    eqeltri
    cP
    cvv
    vx
    hash1snb
    ax-mp
    sylib
    wph
    @2
    wa
    #
    cA
    @0
    cB
    @5
    cA
    @1
    wcel
    cA
    @0
    wceq
    @5
    cA
    cP
    @1
    wph
    cA
    cP
    wcel
    @2
    tgldim0.a
    adantr
    wph
    @2
    simpr
    #
    eleqtrd
    cA
    @0
    elsni
    syl
    @5
    cB
    @1
    wcel
    cB
    @0
    wceq
    @5
    cB
    cP
    @1
    wph
    cB
    cP
    wcel
    @2
    tgldim0.b
    adantr
    @6
    eleqtrd
    cB
    @0
    elsni
    syl
    eqtr4d
    exlimddv
end
