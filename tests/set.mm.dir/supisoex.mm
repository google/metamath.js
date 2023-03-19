include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cima.mm"
include "wiso.mm"
include "wss.mm"
include "wcel.mm"
include "cfv.mm"
include "simpl.mm"
include "simpr.mm"
include "supisolem.mm"
include "wf1o.mm"
include "wf.mm"
include "isof1o.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "breq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "ex.mm"
include "syl.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem supisoex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cD: class D
  assume supiso.1: |- ( ph -> F Isom R , S ( A , B ) )
  assume supiso.2: |- ( ph -> C C_ A )
  assume supisoex.3: |- ( ph -> E. x e. A ( A. y e. C -. x R y /\ A. y e. A ( y R x -> E. z e. C y R z ) ) )

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
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph u
  disjoint ph w
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R u
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D w
  disjoint D y
  disjoint D z
  assert |- ( ph -> E. u e. B ( A. w e. ( F " C ) -. u S w /\ A. w e. B ( w S u -> E. v e. ( F " C ) w S v ) ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cC
    wral
    @1
    @0
    cR
    wbr
    @1
    vz
    cv
    cR
    wbr
    vz
    cC
    wrex
    wi
    vy
    cA
    wral
    wa
    #
    vx
    cA
    wrex
    #
    vu
    cv
    #
    vw
    cv
    #
    cS
    wbr
    #
    wn
    #
    vw
    cF
    cC
    cima
    #
    wral
    #
    @5
    @4
    cS
    wbr
    #
    @5
    vv
    cv
    cS
    wbr
    vv
    @8
    wrex
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vu
    cB
    wrex
    #
    supisoex.3
    wph
    cA
    cB
    cR
    cS
    cF
    wiso
    #
    cC
    cA
    wss
    #
    @3
    @15
    wi
    supiso.1
    supiso.2
    @16
    @17
    wa
    #
    @2
    @15
    vx
    cA
    @18
    @0
    cA
    wcel
    wa
    #
    @2
    @0
    cF
    cfv
    #
    @5
    cS
    wbr
    #
    wn
    #
    vw
    @8
    wral
    #
    @5
    @20
    cS
    wbr
    #
    @11
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    @15
    @18
    vy
    vz
    vw
    vv
    cA
    cB
    cC
    @0
    cR
    cS
    cF
    @16
    @17
    simpl
    #
    @16
    @17
    simpr
    supisolem
    @19
    @20
    cB
    wcel
    #
    @27
    @15
    wi
    @18
    cA
    cB
    @0
    cF
    @18
    @16
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf
    @28
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
    ffvelrnda
    @29
    @27
    @15
    @14
    @27
    vu
    @20
    cB
    @4
    @20
    wceq
    #
    @9
    @23
    @13
    @26
    @30
    @7
    @22
    vw
    @8
    @30
    @6
    @21
    @4
    @20
    @5
    cS
    breq1
    notbid
    ralbidv
    @30
    @12
    @25
    vw
    cB
    @30
    @10
    @24
    @11
    @4
    @20
    @5
    cS
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    ex
    syl
    sylbid
    rexlimdva
    syl2anc
    mpd
end
