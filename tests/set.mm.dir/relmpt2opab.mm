include "co.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "copab.mm"
include "wral.mm"
include "relopab.mm"
include "df-rel.mm"
include "mpbi.mm"
include "rgen2w.mm"
include "ovmptss.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem relmpt2opab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume relmpt2opab.1: |- F = ( x e. A , y e. B |-> { <. z , w >. | ph } )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint A x
  disjoint A y
  assert |- Rel ( C F D )

  proof
    cC
    cD
    cF
    co
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
    vz
    vw
    copab
    #
    @1
    wss
    #
    vy
    cB
    wral
    vx
    cA
    wral
    @2
    @4
    vx
    vy
    cA
    cB
    @3
    wrel
    @4
    wph
    vz
    vw
    relopab
    @3
    df-rel
    mpbi
    rgen2w
    vx
    vy
    cA
    cB
    @3
    cC
    cF
    cD
    @1
    relmpt2opab.1
    ovmptss
    ax-mp
    @0
    df-rel
    mpbir
end
