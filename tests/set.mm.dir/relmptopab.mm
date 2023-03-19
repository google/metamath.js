include "cfv.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "copab.mm"
include "fvmptss.mm"
include "cv.mm"
include "wcel.mm"
include "relopab.mm"
include "df-rel.mm"
include "mpbi.mm"
include "a1i.mm"
include "mprg.mm"
include "mpbir.mm"

theorem relmptopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  assume relmptopab.1: |- F = ( x e. A |-> { <. y , z >. | ph } )

  disjoint A x
  assert |- Rel ( F ` B )

  proof
    cB
    cF
    cfv
    #
    wrel
    @0
    cvv
    cvv
    cxp
    #
    wss
    #
    wph
    vy
    vz
    copab
    #
    @1
    wss
    #
    @2
    vx
    cA
    vx
    cA
    @3
    @1
    cB
    cF
    relmptopab.1
    fvmptss
    @4
    vx
    cv
    cA
    wcel
    @3
    wrel
    @4
    wph
    vy
    vz
    relopab
    @3
    df-rel
    mpbi
    a1i
    mprg
    @0
    df-rel
    mpbir
end
