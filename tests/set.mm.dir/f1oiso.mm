include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wbr.mm"
include "wrex.mm"
include "copab.mm"
include "wb.mm"
include "wral.mm"
include "wiso.mm"
include "simpl.mm"
include "wf1.mm"
include "f1of1.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "eleq2.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "anbi2d.mm"
include "opelopab.mm"
include "weq.mm"
include "anass.mm"
include "f1fveq.mm"
include "equcom.mm"
include "syl6bb.mm"
include "anassrs.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "r19.42v.mm"
include "rexbidva.mm"
include "breq1.mm"
include "ceqsrexv.mm"
include "adantl.mm"
include "bitrd.mm"
include "breq2.mm"
include "sylan9bb.mm"
include "anandis.mm"
include "sylan9bbr.mm"
include "an32s.mm"
include "syl5rbb.mm"
include "ralrimivva.mm"
include "sylan.mm"
include "df-isom.mm"
include "sylanbrc.mm"

theorem f1oiso
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint v x
  disjoint u x
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B v
  disjoint B u
  disjoint H v
  disjoint H u
  disjoint R v
  disjoint R u
  disjoint S v
  disjoint S u
  assert |- ( ( H : A -1-1-onto-> B /\ S = { <. z , w >. | E. x e. A E. y e. A ( ( z = ( H ` x ) /\ w = ( H ` y ) ) /\ x R y ) } ) -> H Isom R , S ( A , B ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    cS
    vz
    cv
    #
    vx
    cv
    #
    cH
    cfv
    #
    wceq
    #
    vw
    cv
    #
    vy
    cv
    #
    cH
    cfv
    #
    wceq
    #
    wa
    #
    @2
    @6
    cR
    wbr
    #
    wa
    #
    vy
    cA
    wrex
    vx
    cA
    wrex
    #
    vz
    vw
    copab
    #
    wceq
    #
    wa
    @0
    vv
    cv
    #
    vu
    cv
    #
    cR
    wbr
    #
    @15
    cH
    cfv
    #
    @16
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vu
    cA
    wral
    vv
    cA
    wral
    #
    cA
    cB
    cR
    cS
    cH
    wiso
    @0
    @14
    simpl
    @0
    cA
    cB
    cH
    wf1
    #
    @14
    @22
    cA
    cB
    cH
    f1of1
    @23
    @14
    wa
    #
    @21
    vv
    vu
    cA
    cA
    @20
    @18
    @19
    cop
    #
    cS
    wcel
    #
    @24
    @15
    cA
    wcel
    #
    @16
    cA
    wcel
    #
    wa
    #
    wa
    @17
    @18
    @19
    cS
    df-br
    @23
    @29
    @14
    @26
    @17
    wb
    @14
    @26
    @25
    @13
    wcel
    #
    @23
    @29
    wa
    #
    @17
    cS
    @13
    @25
    eleq2
    @30
    @18
    @3
    wceq
    #
    @19
    @7
    wceq
    #
    wa
    #
    @10
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    @31
    @17
    @12
    @32
    @8
    wa
    #
    @10
    wa
    #
    vy
    cA
    wrex
    vx
    cA
    wrex
    @37
    vz
    vw
    @18
    @19
    @15
    cH
    fvex
    @16
    cH
    fvex
    @1
    @18
    wceq
    #
    @11
    @39
    vx
    vy
    cA
    cA
    @40
    @9
    @38
    @10
    @40
    @4
    @32
    @8
    @1
    @18
    @3
    eqeq1
    anbi1d
    anbi1d
    2rexbidv
    @5
    @19
    wceq
    #
    @39
    @35
    vx
    vy
    cA
    cA
    @41
    @38
    @34
    @10
    @41
    @8
    @33
    @32
    @5
    @19
    @7
    eqeq1
    anbi2d
    anbi1d
    2rexbidv
    opelopab
    @23
    @27
    @28
    @37
    @17
    wb
    @23
    @27
    wa
    #
    @37
    @33
    @15
    @6
    cR
    wbr
    #
    wa
    #
    vy
    cA
    wrex
    #
    @23
    @28
    wa
    #
    @17
    @42
    @37
    vx
    vv
    weq
    #
    @33
    @10
    wa
    #
    vy
    cA
    wrex
    #
    wa
    #
    vx
    cA
    wrex
    #
    @45
    @42
    @36
    @50
    vx
    cA
    @42
    @2
    cA
    wcel
    #
    wa
    #
    @36
    @47
    @48
    wa
    #
    vy
    cA
    wrex
    @50
    @53
    @35
    @54
    vy
    cA
    @35
    @32
    @48
    wa
    @53
    @54
    @32
    @33
    @10
    anass
    @53
    @32
    @47
    @48
    @23
    @27
    @52
    @32
    @47
    wb
    @23
    @27
    @52
    wa
    wa
    @32
    vv
    vx
    weq
    @47
    cA
    cB
    @15
    @2
    cH
    f1fveq
    vv
    vx
    equcom
    syl6bb
    anassrs
    anbi1d
    syl5bb
    rexbidv
    @47
    @48
    vy
    cA
    r19.42v
    syl6bb
    rexbidva
    @27
    @51
    @45
    wb
    @23
    @49
    @45
    vx
    @15
    cA
    @47
    @48
    @44
    vy
    cA
    @47
    @10
    @43
    @33
    @2
    @15
    @6
    cR
    breq1
    anbi2d
    rexbidv
    ceqsrexv
    adantl
    bitrd
    @46
    @45
    vy
    vu
    weq
    #
    @43
    wa
    #
    vy
    cA
    wrex
    #
    @17
    @46
    @44
    @56
    vy
    cA
    @46
    @6
    cA
    wcel
    #
    wa
    @33
    @55
    @43
    @23
    @28
    @58
    @33
    @55
    wb
    @23
    @28
    @58
    wa
    wa
    @33
    vu
    vy
    weq
    @55
    cA
    cB
    @16
    @6
    cH
    f1fveq
    vu
    vy
    equcom
    syl6bb
    anassrs
    anbi1d
    rexbidva
    @28
    @57
    @17
    wb
    @23
    @43
    @17
    vy
    @16
    cA
    @6
    @16
    @15
    cR
    breq2
    ceqsrexv
    adantl
    bitrd
    sylan9bb
    anandis
    syl5bb
    sylan9bbr
    an32s
    syl5rbb
    ralrimivva
    sylan
    vv
    vu
    cA
    cB
    cR
    cS
    cH
    df-isom
    sylanbrc
end
