include "cnp.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "cltq.mm"
include "wbr.mm"
include "cmq.mm"
include "co.mm"
include "cplq.mm"
include "cpp.mm"
include "cmp.mm"
include "cnq.mm"
include "wb.mm"
include "simpl2.mm"
include "simprlr.mm"
include "elprnq.mm"
include "syl2anc.mm"
include "simp1.mm"
include "simprl.mm"
include "syl2an.mm"
include "simpl3.mm"
include "simprrr.mm"
include "vex.mm"
include "ltmnq.mm"
include "mulcomnq.mm"
include "caovord2.mm"
include "mulclnq.mm"
include "ovex.mm"
include "ltanq.mm"
include "addcomnq.mm"
include "syl.mm"
include "sylan9bb.mm"
include "syl12anc.mm"
include "wi.mm"
include "simpl1.mm"
include "addclpr.mm"
include "3adant1.mm"
include "adantr.mm"
include "mulclpr.mm"
include "distrnq.mm"
include "simprrl.mm"
include "df-plp.mm"
include "addclnq.mm"
include "genpprecl.mm"
include "imp.mm"
include "syl22anc.mm"
include "df-mp.mm"
include "syl5eqelr.mm"
include "prcdnq.mm"
include "sylbid.mm"
include "simpll.mm"
include "sylan9bbr.mm"
include "syl21anc.mm"
include "simprll.mm"
include "wo.mm"
include "wn.mm"
include "weq.mm"
include "wor.mm"
include "ltsonq.mm"
include "sotrieq.mm"
include "mpan.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "sylbird.mm"
include "ecase3d.mm"

theorem distrlem4pr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vg: setvar g
  let vh: setvar h

  disjoint x y
  disjoint x z
  disjoint f x
  disjoint A x
  disjoint y z
  disjoint f y
  disjoint A y
  disjoint f z
  disjoint A z
  disjoint A f
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C f
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint g x
  disjoint h x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint g y
  disjoint h y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint g z
  disjoint h z
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint A w
  disjoint u v
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint A v
  disjoint f u
  disjoint g u
  disjoint h u
  disjoint A u
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint B g
  disjoint B h
  disjoint C w
  disjoint C v
  disjoint C u
  disjoint C g
  disjoint C h
  assert |- ( ( ( A e. P. /\ B e. P. /\ C e. P. ) /\ ( ( x e. A /\ y e. B ) /\ ( f e. A /\ z e. C ) ) ) -> ( ( x .Q y ) +Q ( f .Q z ) ) e. ( A .P. ( B +P. C ) ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    cC
    cnp
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vf
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cC
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    @4
    @9
    cltq
    wbr
    #
    @9
    @4
    cltq
    wbr
    #
    @4
    @6
    cmq
    co
    #
    @9
    @11
    cmq
    co
    #
    cplq
    co
    #
    cA
    cB
    cC
    cpp
    co
    #
    cmp
    co
    #
    wcel
    #
    @15
    @16
    @20
    @9
    @6
    cmq
    co
    #
    @19
    cplq
    co
    #
    cltq
    wbr
    #
    @23
    @15
    @6
    cnq
    wcel
    #
    @9
    cnq
    wcel
    #
    @11
    cnq
    wcel
    #
    @16
    @26
    wb
    @15
    @1
    @7
    @27
    @0
    @1
    @2
    @14
    simpl2
    #
    @3
    @5
    @7
    @13
    simprlr
    #
    cB
    @6
    elprnq
    syl2anc
    #
    @3
    @0
    @10
    @28
    @14
    @0
    @1
    @2
    simp1
    #
    @8
    @10
    @12
    simprl
    cA
    @9
    elprnq
    syl2an
    #
    @15
    @2
    @12
    @29
    @0
    @1
    @2
    @14
    simpl3
    #
    @3
    @8
    @10
    @12
    simprrr
    #
    cC
    @11
    elprnq
    syl2anc
    #
    @27
    @16
    @18
    @24
    cltq
    wbr
    #
    @28
    @29
    wa
    #
    @26
    vw
    vv
    vu
    @4
    @9
    @6
    cltq
    cnq
    cmq
    vx
    vex
    #
    vf
    vex
    #
    vw
    cv
    #
    vv
    cv
    #
    vu
    cv
    #
    ltmnq
    #
    vy
    vex
    @42
    @43
    mulcomnq
    #
    caovord2
    @39
    @19
    cnq
    wcel
    @38
    @26
    wb
    @9
    @11
    mulclnq
    vw
    vv
    vu
    @18
    @24
    @19
    cltq
    cnq
    cplq
    @4
    @6
    cmq
    ovex
    @9
    @6
    cmq
    ovex
    @42
    @43
    @44
    ltanq
    @9
    @11
    cmq
    ovex
    @42
    @43
    addcomnq
    caovord2
    syl
    sylan9bb
    syl12anc
    @15
    @22
    cnp
    wcel
    #
    @25
    @22
    wcel
    @26
    @23
    wi
    @15
    @0
    @21
    cnp
    wcel
    #
    @47
    @0
    @1
    @2
    @14
    simpl1
    #
    @3
    @48
    @14
    @1
    @2
    @48
    @0
    cB
    cC
    addclpr
    3adant1
    adantr
    #
    cA
    @21
    mulclpr
    syl2anc
    #
    @15
    @25
    @9
    @6
    @11
    cplq
    co
    #
    cmq
    co
    #
    @22
    @9
    @6
    @11
    distrnq
    @15
    @0
    @48
    @10
    @52
    @21
    wcel
    #
    @53
    @22
    wcel
    #
    @49
    @50
    @3
    @8
    @10
    @12
    simprrl
    @15
    @1
    @2
    @7
    @12
    @54
    @30
    @35
    @31
    @36
    @1
    @2
    wa
    @7
    @12
    wa
    @54
    vw
    vg
    vh
    vu
    vv
    cB
    cC
    @6
    @11
    cpp
    cplq
    vu
    vv
    vw
    vg
    vh
    df-plp
    vg
    cv
    #
    vh
    cv
    #
    addclnq
    genpprecl
    imp
    syl22anc
    #
    @0
    @48
    wa
    #
    @10
    @54
    wa
    @55
    vw
    vg
    vh
    vu
    vv
    cA
    @21
    @9
    @52
    cmp
    cmq
    vu
    vv
    vw
    vg
    vh
    df-mp
    #
    @56
    @57
    mulclnq
    #
    genpprecl
    imp
    syl22anc
    syl5eqelr
    @22
    @25
    @20
    prcdnq
    syl2anc
    sylbid
    @15
    @17
    @20
    @18
    @4
    @11
    cmq
    co
    #
    cplq
    co
    #
    cltq
    wbr
    #
    @23
    @15
    @4
    cnq
    wcel
    #
    @27
    @29
    @17
    @64
    wb
    @3
    @0
    @5
    @65
    @14
    @33
    @5
    @7
    @13
    simpll
    cA
    @4
    elprnq
    syl2an
    #
    @32
    @37
    @29
    @17
    @19
    @62
    cltq
    wbr
    #
    @65
    @27
    wa
    #
    @64
    vw
    vv
    vu
    @9
    @4
    @11
    cltq
    cnq
    cmq
    @41
    @40
    @45
    vz
    vex
    @46
    caovord2
    @68
    @18
    cnq
    wcel
    @67
    @64
    wb
    @4
    @6
    mulclnq
    @19
    @62
    @18
    ltanq
    syl
    sylan9bbr
    syl21anc
    @15
    @47
    @63
    @22
    wcel
    @64
    @23
    wi
    @51
    @15
    @63
    @4
    @52
    cmq
    co
    #
    @22
    @4
    @6
    @11
    distrnq
    #
    @15
    @0
    @48
    @5
    @54
    @69
    @22
    wcel
    #
    @49
    @50
    @3
    @5
    @7
    @13
    simprll
    @58
    @59
    @5
    @54
    wa
    @71
    vw
    vg
    vh
    vu
    vv
    cA
    @21
    @4
    @52
    cmp
    cmq
    @60
    @61
    genpprecl
    imp
    syl22anc
    #
    syl5eqelr
    @22
    @63
    @20
    prcdnq
    syl2anc
    sylbid
    @15
    @16
    @17
    wo
    wn
    #
    vx
    vf
    weq
    #
    @23
    @15
    @65
    @28
    @74
    @73
    wb
    #
    @66
    @34
    cnq
    cltq
    wor
    @65
    @28
    wa
    @75
    ltsonq
    cnq
    @4
    @9
    cltq
    sotrieq
    mpan
    syl2anc
    @15
    @71
    @74
    @23
    @72
    @74
    @69
    @20
    @22
    @74
    @69
    @63
    @20
    @70
    @74
    @62
    @19
    @18
    cplq
    @4
    @9
    @11
    cmq
    oveq1
    oveq2d
    syl5eq
    eleq1d
    syl5ibcom
    sylbird
    ecase3d
end
