include "wpo.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "csb.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "impcom.mm"
include "poirr.mm"
include "cop.mm"
include "copab.mm"
include "df-br.mm"
include "eleq2i.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "vex.mm"
include "breq1d.mm"
include "csbie.mm"
include "csbeq1.mm"
include "syl5eqr.mm"
include "breq2d.mm"
include "opelopabf.mm"
include "3bitri.mm"
include "sylnibr.mm"
include "sylan2.mm"
include "anassrs.mm"
include "w3a.mm"
include "wi.mm"
include "com12.mm"
include "3anim123d.mm"
include "imp.mm"
include "adantll.mm"
include "potr.mm"
include "anbi12i.mm"
include "3imtr4g.mm"
include "adantlr.mm"
include "syldan.mm"
include "ispod.mm"

theorem pofun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume pofun.1: |- S = { <. x , y >. | X R Y }
  assume pofun.2: |- ( x = y -> X = Y )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint X y
  disjoint Y x
  disjoint A x
  disjoint B x
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Y z
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint B v
  disjoint B w
  disjoint B z
  assert |- ( ( R Po B /\ A. x e. A X e. B ) -> S Po A )

  proof
    cB
    cR
    wpo
    #
    cX
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vv
    vw
    vz
    cA
    cS
    @0
    @2
    vv
    cv
    #
    cA
    wcel
    #
    @4
    @4
    cS
    wbr
    #
    wn
    #
    @2
    @5
    wa
    @0
    vx
    @4
    cX
    csb
    #
    cB
    wcel
    #
    @7
    @5
    @2
    @9
    @1
    @9
    vx
    @4
    cA
    vx
    @8
    cB
    vx
    @4
    cX
    nfcsb1v
    #
    nfel1
    vx
    vv
    weq
    #
    cX
    @8
    cB
    vx
    @4
    cX
    csbeq1a
    #
    eleq1d
    rspc
    #
    impcom
    @0
    @9
    wa
    @8
    @8
    cR
    wbr
    #
    @6
    cB
    @8
    cR
    poirr
    @6
    @4
    @4
    cop
    #
    cS
    wcel
    @15
    cX
    cY
    cR
    wbr
    #
    vx
    vy
    copab
    #
    wcel
    @14
    @4
    @4
    cS
    df-br
    cS
    @17
    @15
    pofun.1
    eleq2i
    @16
    @8
    cY
    cR
    wbr
    #
    @14
    vx
    vy
    @4
    @4
    vx
    @8
    cY
    cR
    @10
    vx
    cR
    nfcv
    #
    vx
    cY
    nfcv
    #
    nfbr
    #
    @14
    vy
    nfv
    vv
    vex
    #
    @22
    @11
    cX
    @8
    cY
    cR
    @12
    breq1d
    #
    vy
    vv
    weq
    #
    cY
    @8
    @8
    cR
    @24
    cY
    vx
    vy
    cv
    #
    cX
    csb
    #
    @8
    vx
    @25
    cX
    cY
    vy
    vex
    pofun.2
    csbie
    #
    vx
    @25
    @4
    cX
    csbeq1
    syl5eqr
    breq2d
    opelopabf
    3bitri
    sylnibr
    sylan2
    anassrs
    @3
    @5
    vw
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    w3a
    #
    @9
    vx
    @28
    cX
    csb
    #
    cB
    wcel
    #
    vx
    @30
    cX
    csb
    #
    cB
    wcel
    #
    w3a
    #
    @4
    @28
    cS
    wbr
    #
    @28
    @30
    cS
    wbr
    #
    wa
    #
    @4
    @30
    cS
    wbr
    #
    wi
    #
    @2
    @32
    @37
    @0
    @2
    @32
    @37
    @2
    @5
    @9
    @29
    @34
    @31
    @36
    @5
    @2
    @9
    @13
    com12
    @29
    @2
    @34
    @1
    @34
    vx
    @28
    cA
    vx
    @33
    cB
    vx
    @28
    cX
    nfcsb1v
    #
    nfel1
    vx
    vw
    weq
    #
    cX
    @33
    cB
    vx
    @28
    cX
    csbeq1a
    #
    eleq1d
    rspc
    com12
    @31
    @2
    @36
    @1
    @36
    vx
    @30
    cA
    vx
    @35
    cB
    vx
    @30
    cX
    nfcsb1v
    nfel1
    vx
    vz
    weq
    cX
    @35
    cB
    vx
    @30
    cX
    csbeq1a
    eleq1d
    rspc
    com12
    3anim123d
    imp
    adantll
    @0
    @37
    @42
    @2
    @0
    @37
    wa
    @8
    @33
    cR
    wbr
    #
    @33
    @35
    cR
    wbr
    #
    wa
    @8
    @35
    cR
    wbr
    #
    @40
    @41
    cB
    @8
    @33
    @35
    cR
    potr
    @38
    @46
    @39
    @47
    @38
    @4
    @28
    cop
    #
    cS
    wcel
    @49
    @17
    wcel
    @46
    @4
    @28
    cS
    df-br
    cS
    @17
    @49
    pofun.1
    eleq2i
    @16
    @18
    @46
    vx
    vy
    @4
    @28
    @21
    @46
    vy
    nfv
    @22
    vw
    vex
    #
    @23
    vy
    vw
    weq
    #
    cY
    @33
    @8
    cR
    @51
    cY
    @26
    @33
    @27
    vx
    @25
    @28
    cX
    csbeq1
    syl5eqr
    breq2d
    opelopabf
    3bitri
    @39
    @28
    @30
    cop
    #
    cS
    wcel
    @52
    @17
    wcel
    @47
    @28
    @30
    cS
    df-br
    cS
    @17
    @52
    pofun.1
    eleq2i
    @16
    @33
    cY
    cR
    wbr
    @47
    vx
    vy
    @28
    @30
    vx
    @33
    cY
    cR
    @43
    @19
    @20
    nfbr
    @47
    vy
    nfv
    @50
    vz
    vex
    #
    @44
    cX
    @33
    cY
    cR
    @45
    breq1d
    vy
    vz
    weq
    #
    cY
    @35
    @33
    cR
    @54
    cY
    @26
    @35
    @27
    vx
    @25
    @30
    cX
    csbeq1
    syl5eqr
    #
    breq2d
    opelopabf
    3bitri
    anbi12i
    @41
    @4
    @30
    cop
    #
    cS
    wcel
    @56
    @17
    wcel
    @48
    @4
    @30
    cS
    df-br
    cS
    @17
    @56
    pofun.1
    eleq2i
    @16
    @18
    @48
    vx
    vy
    @4
    @30
    @21
    @48
    vy
    nfv
    @22
    @53
    @23
    @54
    cY
    @35
    @8
    cR
    @55
    breq2d
    opelopabf
    3bitri
    3imtr4g
    adantlr
    syldan
    ispod
end
