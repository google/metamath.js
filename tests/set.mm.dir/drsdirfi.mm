include "cdrs.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "raleq.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "wne.mm"
include "drsbn0.mm"
include "wex.mm"
include "ral0.mm"
include "jctr.mm"
include "eximi.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4i.mm"
include "syl.mm"
include "adantr.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "anim2i.mm"
include "breq2.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "simplrr.mm"
include "cpreset.mm"
include "drsprs.mm"
include "ad5antr.mm"
include "ad2antlr.mm"
include "sselda.mm"
include "simp-4r.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simprrl.mm"
include "prstr.mm"
include "syl132anc.mm"
include "ex.mm"
include "ralimdva.mm"
include "adantlrr.mm"
include "mpd.mm"
include "simprrr.mm"
include "vex.mm"
include "breq1.mm"
include "ralsn.mm"
include "sylibr.mm"
include "ralun.mm"
include "syl2anc.mm"
include "simpll.mm"
include "ssun2.mm"
include "snss.mm"
include "drsdir.mm"
include "syl3anc.mm"
include "reximddv.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "embantd.mm"
include "com12.mm"
include "a1i.mm"
include "findcard2.mm"
include "3impia.mm"

theorem drsdirfi
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume drsbn0.b: |- B = ( Base ` K )
  assume drsdirfi.l: |- .<_ = ( le ` K )

  disjoint K y
  disjoint K z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint .<_ y
  disjoint .<_ z
  disjoint X y
  disjoint X z
  disjoint K x
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .<_ a
  disjoint .<_ b
  disjoint .<_ c
  disjoint .<_ x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X x
  assert |- ( ( K e. Dirset /\ X C_ B /\ X e. Fin ) -> E. y e. B A. z e. X z .<_ y )

  proof
    cK
    cdrs
    wcel
    #
    cX
    cB
    wss
    #
    cX
    cfn
    wcel
    #
    vz
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    vz
    cX
    wral
    #
    vy
    cB
    wrex
    #
    @2
    @0
    @1
    wa
    #
    @7
    @0
    va
    cv
    #
    cB
    wss
    #
    wa
    #
    @5
    vz
    @9
    wral
    #
    vy
    cB
    wrex
    #
    wi
    @0
    c0
    cB
    wss
    #
    wa
    #
    @5
    vz
    c0
    wral
    #
    vy
    cB
    wrex
    #
    wi
    @0
    vb
    cv
    #
    cB
    wss
    #
    wa
    #
    @5
    vz
    @18
    wral
    #
    vy
    cB
    wrex
    #
    wi
    #
    @0
    @18
    vc
    cv
    #
    csn
    #
    cun
    #
    cB
    wss
    #
    wa
    #
    @5
    vz
    @26
    wral
    #
    vy
    cB
    wrex
    #
    wi
    #
    @8
    @7
    wi
    va
    vb
    vc
    cX
    @9
    c0
    wceq
    #
    @11
    @15
    @13
    @17
    @32
    @10
    @14
    @0
    @9
    c0
    cB
    sseq1
    anbi2d
    @32
    @12
    @16
    vy
    cB
    @5
    vz
    @9
    c0
    raleq
    rexbidv
    imbi12d
    @9
    @18
    wceq
    #
    @11
    @20
    @13
    @22
    @33
    @10
    @19
    @0
    @9
    @18
    cB
    sseq1
    anbi2d
    @33
    @12
    @21
    vy
    cB
    @5
    vz
    @9
    @18
    raleq
    rexbidv
    imbi12d
    @9
    @26
    wceq
    #
    @11
    @28
    @13
    @30
    @34
    @10
    @27
    @0
    @9
    @26
    cB
    sseq1
    anbi2d
    @34
    @12
    @29
    vy
    cB
    @5
    vz
    @9
    @26
    raleq
    rexbidv
    imbi12d
    @9
    cX
    wceq
    #
    @11
    @8
    @13
    @7
    @35
    @10
    @1
    @0
    @9
    cX
    cB
    sseq1
    anbi2d
    @35
    @12
    @6
    vy
    cB
    @5
    vz
    @9
    cX
    raleq
    rexbidv
    imbi12d
    @0
    @17
    @14
    @0
    cB
    c0
    wne
    #
    @17
    cB
    cK
    drsbn0.b
    drsbn0
    @4
    cB
    wcel
    #
    vy
    wex
    @37
    @16
    wa
    #
    vy
    wex
    @36
    @17
    @37
    @38
    vy
    @37
    @16
    @5
    vz
    ral0
    jctr
    eximi
    vy
    cB
    n0
    @16
    vy
    cB
    df-rex
    3imtr4i
    syl
    adantr
    @23
    @31
    wi
    @18
    cfn
    wcel
    @28
    @23
    @30
    @28
    @20
    @22
    @30
    @27
    @19
    @0
    @18
    @26
    wss
    @27
    @19
    @18
    @25
    ssun1
    @18
    @26
    cB
    sstr
    mpan
    #
    anim2i
    @22
    @3
    @9
    c.le
    wbr
    #
    vz
    @18
    wral
    #
    va
    cB
    wrex
    @28
    @30
    @21
    @41
    vy
    va
    cB
    @4
    @9
    wceq
    @5
    @40
    vz
    @18
    @4
    @9
    @3
    c.le
    breq2
    ralbidv
    cbvrexv
    @28
    @41
    @30
    va
    cB
    @28
    @9
    cB
    wcel
    #
    @41
    wa
    #
    wa
    #
    @9
    @4
    c.le
    wbr
    #
    @24
    @4
    c.le
    wbr
    #
    wa
    #
    @29
    vy
    cB
    @44
    @37
    @47
    wa
    #
    wa
    #
    @21
    @5
    vz
    @25
    wral
    #
    @29
    @49
    @41
    @21
    @28
    @42
    @41
    @48
    simplrr
    @28
    @42
    @48
    @41
    @21
    wi
    @41
    @28
    @42
    wa
    #
    @48
    wa
    #
    @40
    @5
    vz
    @18
    @52
    @3
    @18
    wcel
    #
    wa
    #
    @40
    @5
    @54
    @40
    wa
    cK
    cpreset
    wcel
    #
    @3
    cB
    wcel
    #
    @42
    @37
    @40
    @45
    @5
    @0
    @55
    @27
    @42
    @48
    @53
    @40
    cK
    drsprs
    ad5antr
    @54
    @56
    @40
    @52
    @18
    cB
    @3
    @51
    @19
    @48
    @27
    @19
    @0
    @42
    @39
    ad2antlr
    adantr
    sselda
    adantr
    @28
    @42
    @48
    @53
    @40
    simp-4r
    @52
    @37
    @53
    @40
    @51
    @37
    @47
    simprl
    ad2antrr
    @54
    @40
    simpr
    @52
    @45
    @53
    @40
    @51
    @37
    @45
    @46
    simprrl
    ad2antrr
    cB
    cK
    c.le
    @3
    @9
    @4
    drsbn0.b
    drsdirfi.l
    prstr
    syl132anc
    ex
    ralimdva
    adantlrr
    mpd
    @49
    @46
    @50
    @44
    @37
    @45
    @46
    simprrr
    @5
    @46
    vz
    @24
    vc
    vex
    #
    @3
    @24
    @4
    c.le
    breq1
    ralsn
    sylibr
    @5
    vz
    @18
    @25
    ralun
    syl2anc
    @44
    @0
    @42
    @24
    cB
    wcel
    #
    @47
    vy
    cB
    wrex
    @0
    @27
    @43
    simpll
    @28
    @42
    @41
    simprl
    @27
    @58
    @0
    @43
    @27
    @25
    cB
    wss
    #
    @58
    @25
    @26
    wss
    @27
    @59
    @25
    @18
    ssun2
    @25
    @26
    cB
    sstr
    mpan
    @24
    cB
    @57
    snss
    sylibr
    ad2antlr
    vy
    cB
    cK
    c.le
    @9
    @24
    drsbn0.b
    drsdirfi.l
    drsdir
    syl3anc
    reximddv
    rexlimdvaa
    syl5bi
    embantd
    com12
    a1i
    findcard2
    com12
    3impia
end
