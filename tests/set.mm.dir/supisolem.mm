include "wiso.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cfv.mm"
include "cima.mm"
include "wb.mm"
include "jca.mm"
include "simpll.mm"
include "adantr.mm"
include "simplr.mm"
include "sselda.mm"
include "isorel.mm"
include "syl12anc.mm"
include "notbid.mm"
include "ralbidva.mm"
include "wfn.mm"
include "wf1o.mm"
include "isof1o.mm"
include "syl.mm"
include "f1ofn.mm"
include "wceq.mm"
include "breq2.mm"
include "ralima.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "simpr.mm"
include "rexbidva.mm"
include "rexima.mm"
include "imbi12d.mm"
include "wfo.mm"
include "f1ofo.mm"
include "breq1.mm"
include "rexbidv.mm"
include "cbvfo.mm"
include "3syl.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "sylan.mm"

theorem supisolem
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let vu: setvar u
  let vx: setvar x
  assume supiso.1: |- ( ph -> F Isom R , S ( A , B ) )
  assume supiso.2: |- ( ph -> C C_ A )

  disjoint v w
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint ph w
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint w x
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint C u
  disjoint C x
  disjoint ph u
  disjoint F u
  disjoint F x
  disjoint R u
  disjoint R x
  disjoint S u
  disjoint S x
  disjoint B u
  disjoint B x
  assert |- ( ( ph /\ D e. A ) -> ( ( A. y e. C -. D R y /\ A. y e. A ( y R D -> E. z e. C y R z ) ) <-> ( A. w e. ( F " C ) -. ( F ` D ) S w /\ A. w e. B ( w S ( F ` D ) -> E. v e. ( F " C ) w S v ) ) ) )

  proof
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
    wa
    #
    cD
    cA
    wcel
    #
    cD
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cC
    wral
    #
    @4
    cD
    cR
    wbr
    #
    @4
    vz
    cv
    #
    cR
    wbr
    #
    vz
    cC
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    cD
    cF
    cfv
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
    @15
    @14
    cS
    wbr
    #
    @15
    vv
    cv
    #
    cS
    wbr
    #
    vv
    @18
    wrex
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    wb
    wph
    @0
    @1
    supiso.1
    supiso.2
    jca
    @2
    @3
    wa
    #
    @7
    @19
    @13
    @25
    @26
    @7
    @14
    @4
    cF
    cfv
    #
    cS
    wbr
    #
    wn
    #
    vy
    cC
    wral
    #
    @19
    @26
    @6
    @29
    vy
    cC
    @26
    @4
    cC
    wcel
    #
    wa
    #
    @5
    @28
    @32
    @0
    @3
    @4
    cA
    wcel
    #
    @5
    @28
    wb
    @26
    @0
    @31
    @0
    @1
    @3
    simpll
    #
    adantr
    @2
    @3
    @31
    simplr
    @26
    cC
    cA
    @4
    @0
    @1
    @3
    simplr
    #
    sselda
    cA
    cB
    cD
    @4
    cR
    cS
    cF
    isorel
    syl12anc
    notbid
    ralbidva
    @26
    cF
    cA
    wfn
    #
    @1
    @19
    @30
    wb
    @26
    cA
    cB
    cF
    wf1o
    #
    @36
    @26
    @0
    @37
    @34
    cA
    cB
    cR
    cS
    cF
    isof1o
    syl
    #
    cA
    cB
    cF
    f1ofn
    syl
    #
    @35
    @17
    @29
    vw
    vy
    cA
    cC
    cF
    @15
    @27
    wceq
    @16
    @28
    @15
    @27
    @14
    cS
    breq2
    notbid
    ralima
    syl2anc
    bitr4d
    @26
    @13
    @27
    @14
    cS
    wbr
    #
    @27
    @21
    cS
    wbr
    #
    vv
    @18
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    @25
    @26
    @12
    @43
    vy
    cA
    @26
    @33
    wa
    #
    @8
    @40
    @11
    @42
    @45
    @0
    @33
    @3
    @8
    @40
    wb
    @26
    @0
    @33
    @34
    adantr
    #
    @26
    @33
    simpr
    @2
    @3
    @33
    simplr
    cA
    cB
    @4
    cD
    cR
    cS
    cF
    isorel
    syl12anc
    @45
    @11
    @27
    @9
    cF
    cfv
    #
    cS
    wbr
    #
    vz
    cC
    wrex
    #
    @42
    @45
    @10
    @48
    vz
    cC
    @45
    @9
    cC
    wcel
    #
    wa
    @0
    @33
    @9
    cA
    wcel
    @10
    @48
    wb
    @45
    @0
    @50
    @46
    adantr
    @26
    @33
    @50
    simplr
    @45
    cC
    cA
    @9
    @26
    @1
    @33
    @35
    adantr
    #
    sselda
    cA
    cB
    @4
    @9
    cR
    cS
    cF
    isorel
    syl12anc
    rexbidva
    @45
    @36
    @1
    @42
    @49
    wb
    @26
    @36
    @33
    @39
    adantr
    @51
    @41
    @48
    vv
    vz
    cA
    cC
    cF
    @21
    @47
    @27
    cS
    breq2
    rexima
    syl2anc
    bitr4d
    imbi12d
    ralbidva
    @26
    @37
    cA
    cB
    cF
    wfo
    @44
    @25
    wb
    @38
    cA
    cB
    cF
    f1ofo
    @43
    @24
    vy
    vw
    cA
    cB
    cF
    @27
    @15
    wceq
    #
    @40
    @20
    @42
    @23
    @27
    @15
    @14
    cS
    breq1
    @52
    @41
    @22
    vv
    @18
    @27
    @15
    @21
    cS
    breq1
    rexbidv
    imbi12d
    cbvfo
    3syl
    bitrd
    anbi12d
    sylan
end
