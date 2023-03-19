include "cima.mm"
include "csup.mm"
include "cfv.mm"
include "wor.mm"
include "wiso.mm"
include "wb.mm"
include "isoso.mm"
include "syl.mm"
include "mpbid.mm"
include "wf1o.mm"
include "wf.mm"
include "isof1o.mm"
include "f1of.mm"
include "3syl.mm"
include "supcl.mm"
include "ffvelrnd.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "supub.mm"
include "ralrimiv.mm"
include "wcel.mm"
include "suplub.mm"
include "expd.mm"
include "supisolem.mm"
include "mpdan.mm"
include "mpbi2and.mm"
include "simpld.mm"
include "r19.21bi.mm"
include "simprd.mm"
include "impr.mm"
include "eqsupd.mm"

theorem supiso
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cD: class D
  assume supiso.1: |- ( ph -> F Isom R , S ( A , B ) )
  assume supiso.2: |- ( ph -> C C_ A )
  assume supisoex.3: |- ( ph -> E. x e. A ( A. y e. C -. x R y /\ A. y e. A ( y R x -> E. z e. C y R z ) ) )
  assume supiso.4: |- ( ph -> R Or A )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint ph u
  disjoint ph w
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint R u
  disjoint R w
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint B u
  disjoint B v
  disjoint B w
  assert |- ( ph -> sup ( ( F " C ) , B , S ) = ( F ` sup ( C , A , R ) ) )

  proof
    wph
    vw
    vv
    cB
    cF
    cC
    cima
    #
    cC
    cA
    cR
    csup
    #
    cF
    cfv
    #
    cS
    wph
    cA
    cR
    wor
    #
    cB
    cS
    wor
    #
    supiso.4
    wph
    cA
    cB
    cR
    cS
    cF
    wiso
    #
    @3
    @4
    wb
    supiso.1
    cA
    cB
    cR
    cS
    cF
    isoso
    syl
    mpbid
    wph
    cA
    cB
    @1
    cF
    wph
    @5
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf
    supiso.1
    cA
    cB
    cR
    cS
    cF
    isof1o
    cA
    cB
    cF
    f1of
    3syl
    wph
    vx
    vy
    vz
    cA
    cC
    cR
    supiso.4
    supisoex.3
    supcl
    #
    ffvelrnd
    wph
    @2
    vw
    cv
    #
    cS
    wbr
    wn
    #
    vw
    @0
    wph
    @8
    vw
    @0
    wral
    #
    @7
    @2
    cS
    wbr
    #
    @7
    vv
    cv
    cS
    wbr
    vv
    @0
    wrex
    #
    wi
    #
    vw
    cB
    wral
    #
    wph
    @1
    vu
    cv
    #
    cR
    wbr
    wn
    #
    vu
    cC
    wral
    #
    @14
    @1
    cR
    wbr
    #
    @14
    vz
    cv
    cR
    wbr
    vz
    cC
    wrex
    #
    wi
    #
    vu
    cA
    wral
    #
    @9
    @13
    wa
    #
    wph
    @15
    vu
    cC
    wph
    vx
    vy
    vz
    cA
    cC
    @14
    cR
    supiso.4
    supisoex.3
    supub
    ralrimiv
    wph
    @19
    vu
    cA
    wph
    @14
    cA
    wcel
    @17
    @18
    wph
    vx
    vy
    vz
    cA
    cC
    @14
    cR
    supiso.4
    supisoex.3
    suplub
    expd
    ralrimiv
    wph
    @1
    cA
    wcel
    @16
    @20
    wa
    @21
    wb
    @6
    wph
    vu
    vz
    vw
    vv
    cA
    cB
    cC
    @1
    cR
    cS
    cF
    supiso.1
    supiso.2
    supisolem
    mpdan
    mpbi2and
    #
    simpld
    r19.21bi
    wph
    @7
    cB
    wcel
    @10
    @11
    wph
    @12
    vw
    cB
    wph
    @9
    @13
    @22
    simprd
    r19.21bi
    impr
    eqsupd
end
