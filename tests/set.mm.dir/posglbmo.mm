include "cpo.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "weq.mm"
include "wrmo.mm"
include "simplrr.mm"
include "simprlr.mm"
include "simprrl.mm"
include "breq1.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "simplrl.mm"
include "simprrr.mm"
include "simprll.mm"
include "wb.mm"
include "w3a.mm"
include "ancom.mm"
include "posasymb.mm"
include "syl5bb.mm"
include "3expb.mm"
include "ad4ant13.mm"
include "mpbi2and.mm"
include "ex.mm"
include "ralrimivva.mm"
include "breq2.mm"
include "imbi2d.mm"
include "anbi12d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem posglbmo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cK: class K
  let c.le: class .<_
  let vw: setvar w
  assume poslubmo.l: |- .<_ = ( le ` K )
  assume poslubmo.b: |- B = ( Base ` K )

  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint .<_ w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint K w
  disjoint S w
  assert |- ( ( K e. Poset /\ S C_ B ) -> E* x e. B ( A. y e. S x .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) )

  proof
    cK
    cpo
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    vz
    cv
    #
    @4
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @7
    @3
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vw
    cv
    #
    @4
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @9
    @7
    @14
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    wa
    #
    vx
    vw
    weq
    #
    wi
    #
    vw
    cB
    wral
    vx
    cB
    wral
    @13
    vx
    cB
    wrmo
    @2
    @23
    vx
    vw
    cB
    cB
    @2
    @3
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    wa
    #
    wa
    #
    @21
    @22
    @27
    @21
    wa
    #
    @14
    @3
    c.le
    wbr
    #
    @3
    @14
    c.le
    wbr
    #
    @22
    @28
    @25
    @12
    @16
    @29
    @2
    @24
    @25
    @21
    simplrr
    @27
    @6
    @12
    @20
    simprlr
    @27
    @13
    @16
    @19
    simprrl
    @11
    @16
    @29
    wi
    vz
    @14
    cB
    vz
    vw
    weq
    #
    @9
    @16
    @10
    @29
    @31
    @8
    @15
    vy
    cS
    @7
    @14
    @4
    c.le
    breq1
    ralbidv
    @7
    @14
    @3
    c.le
    breq1
    imbi12d
    rspcv
    syl3c
    @28
    @24
    @19
    @6
    @30
    @2
    @24
    @25
    @21
    simplrl
    @27
    @13
    @16
    @19
    simprrr
    @27
    @6
    @12
    @20
    simprll
    @18
    @6
    @30
    wi
    vz
    @3
    cB
    vz
    vx
    weq
    #
    @9
    @6
    @17
    @30
    @32
    @8
    @5
    vy
    cS
    @7
    @3
    @4
    c.le
    breq1
    ralbidv
    @7
    @3
    @14
    c.le
    breq1
    imbi12d
    rspcv
    syl3c
    @0
    @26
    @29
    @30
    wa
    #
    @22
    wb
    #
    @1
    @21
    @0
    @24
    @25
    @34
    @33
    @30
    @29
    wa
    @0
    @24
    @25
    w3a
    @22
    @29
    @30
    ancom
    cB
    cK
    c.le
    @3
    @14
    poslubmo.b
    poslubmo.l
    posasymb
    syl5bb
    3expb
    ad4ant13
    mpbi2and
    ex
    ralrimivva
    @13
    @20
    vx
    vw
    cB
    @22
    @6
    @16
    @12
    @19
    @22
    @5
    @15
    vy
    cS
    @3
    @14
    @4
    c.le
    breq1
    ralbidv
    @22
    @11
    @18
    vz
    cB
    @22
    @10
    @17
    @9
    @3
    @14
    @7
    c.le
    breq2
    imbi2d
    ralbidv
    anbi12d
    rmo4
    sylibr
end
