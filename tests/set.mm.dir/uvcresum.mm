include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cof.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "frlmbasf.mm"
include "3adant1.mm"
include "feqmptd.mm"
include "wa.mm"
include "c0g.mm"
include "cmnd.mm"
include "simpl1.mm"
include "ringmnd.mm"
include "syl.mm"
include "simpl2.mm"
include "simpr.mm"
include "wral.mm"
include "csn.mm"
include "cxp.mm"
include "ffvelrnda.mm"
include "uvcff.mm"
include "3adant3.mm"
include "frlmvscafval.mm"
include "adantr.mm"
include "syl2anc.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "offval2.mm"
include "eqtrd.mm"
include "clmod.mm"
include "csca.mm"
include "frlmlmod.mm"
include "frlmsca.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "fmptd.mm"
include "wne.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "uvcvv0.mm"
include "oveq2d.mm"
include "adantlr.mm"
include "ringrz.mm"
include "suppsssn.mm"
include "gsumpt.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cur.mm"
include "uvcvv1.mm"
include "ringridm.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "simp1.mm"
include "cvv.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "wss.mm"
include "cfsupp.mm"
include "wbr.mm"
include "mptexg.mm"
include "3ad2ant2.mm"
include "funmpt.mm"
include "fvexd.mm"
include "frlmbasfsupp.mm"
include "fsuppimpd.mm"
include "cdif.mm"
include "eqcomd.mm"
include "ssid.mm"
include "syl6eqss.mm"
include "suppssr.mm"
include "oveq1d.mm"
include "eldifi.mm"
include "sylan2.mm"
include "lmod0vs.mm"
include "3eqtr3d.mm"
include "suppss2.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "frlmgsum.mm"

theorem uvcresum
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume uvcresum.u: |- U = ( R unitVec I )
  assume uvcresum.y: |- Y = ( R freeLMod I )
  assume uvcresum.b: |- B = ( Base ` Y )
  assume uvcresum.v: |- .x. = ( .s ` Y )


  assert |- ( ( R e. Ring /\ I e. W /\ X e. B ) -> X = ( Y gsum ( X oF .x. U ) ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cW
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    vb
    cI
    va
    cI
    vb
    cv
    #
    cX
    cfv
    #
    va
    cv
    #
    @4
    cU
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cmpt
    #
    cgsu
    co
    #
    cY
    cX
    cU
    c.x
    cof
    co
    #
    cgsu
    co
    @3
    cX
    va
    cI
    cR
    vb
    cI
    @10
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    @13
    @3
    cX
    va
    cI
    @6
    cX
    cfv
    #
    cmpt
    @17
    @3
    va
    cI
    cR
    cbs
    cfv
    #
    cX
    @1
    @2
    cI
    @19
    cX
    wf
    @0
    cB
    cR
    cY
    cI
    @19
    cW
    cX
    uvcresum.y
    @19
    eqid
    #
    uvcresum.b
    frlmbasf
    3adant1
    #
    feqmptd
    @3
    va
    cI
    @16
    @18
    @3
    @6
    cI
    wcel
    #
    wa
    #
    @16
    @6
    @15
    cfv
    #
    @18
    @23
    cI
    @19
    @15
    cR
    cW
    @6
    cR
    c0g
    cfv
    #
    @20
    @25
    eqid
    #
    @23
    @0
    cR
    cmnd
    wcel
    @0
    @1
    @2
    @22
    simpl1
    #
    cR
    ringmnd
    syl
    @0
    @1
    @2
    @22
    simpl2
    #
    @3
    @22
    simpr
    #
    @23
    vb
    cI
    @10
    @19
    @15
    @3
    @4
    cI
    wcel
    #
    @22
    @10
    @19
    wcel
    #
    @3
    @30
    wa
    #
    @31
    va
    cI
    @32
    cI
    @19
    @11
    wf
    #
    @31
    va
    cI
    wral
    @32
    @1
    @11
    cB
    wcel
    @33
    @0
    @1
    @2
    @30
    simpl2
    #
    @32
    @5
    @7
    c.x
    co
    #
    @11
    cB
    @32
    @35
    cI
    @5
    csn
    cxp
    #
    @7
    @9
    cof
    co
    @11
    @32
    @5
    cB
    cR
    c.x
    @9
    cI
    @19
    cW
    @7
    cY
    uvcresum.y
    uvcresum.b
    @20
    @34
    @3
    cI
    @19
    @4
    cX
    @21
    ffvelrnda
    #
    @3
    cI
    cB
    @4
    cU
    @0
    @1
    cI
    cB
    cU
    wf
    @2
    cB
    cR
    cU
    cI
    cW
    cY
    uvcresum.u
    uvcresum.y
    uvcresum.b
    uvcff
    3adant3
    #
    ffvelrnda
    #
    uvcresum.v
    @9
    eqid
    #
    frlmvscafval
    @32
    va
    cI
    @5
    @8
    @9
    @36
    @7
    cW
    @19
    @19
    @34
    @32
    @5
    @19
    wcel
    #
    @22
    @37
    adantr
    @32
    cI
    @19
    @6
    @7
    @32
    @1
    @7
    cB
    wcel
    #
    cI
    @19
    @7
    wf
    @34
    @39
    cB
    cR
    cY
    cI
    @19
    cW
    @7
    uvcresum.y
    @20
    uvcresum.b
    frlmbasf
    syl2anc
    #
    ffvelrnda
    @36
    va
    cI
    @5
    cmpt
    wceq
    @32
    va
    cI
    @5
    fconstmpt
    a1i
    @32
    va
    cI
    @19
    @7
    @43
    feqmptd
    offval2
    eqtrd
    #
    @32
    cY
    clmod
    wcel
    #
    @5
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @42
    @35
    cB
    wcel
    @3
    @45
    @30
    @0
    @1
    @45
    @2
    cR
    cY
    cI
    cW
    uvcresum.y
    frlmlmod
    3adant3
    #
    adantr
    @32
    @5
    @19
    @47
    @37
    @3
    @19
    @47
    wceq
    @30
    @3
    cR
    @46
    cbs
    @0
    @1
    cR
    @46
    wceq
    @2
    cR
    cY
    cI
    crg
    cW
    uvcresum.y
    frlmsca
    3adant3
    #
    fveq2d
    adantr
    eleqtrd
    @39
    @5
    c.x
    @46
    @47
    cB
    cY
    @7
    uvcresum.b
    @46
    eqid
    #
    uvcresum.v
    @47
    eqid
    lmodvscl
    syl3anc
    eqeltrrd
    #
    cB
    cR
    cY
    cI
    @19
    cW
    @11
    uvcresum.y
    @20
    uvcresum.b
    frlmbasf
    syl2anc
    va
    cI
    @19
    @10
    @11
    @11
    eqid
    fmpt
    sylibr
    r19.21bi
    an32s
    @15
    eqid
    #
    fmptd
    @23
    cI
    @10
    vb
    cW
    @6
    @25
    @23
    @30
    @4
    @6
    wne
    #
    w3a
    #
    @10
    @5
    @25
    @9
    co
    #
    @25
    @54
    @8
    @25
    @5
    @9
    @54
    cR
    cU
    cI
    @4
    @6
    crg
    cW
    @25
    uvcresum.u
    @23
    @30
    @0
    @53
    @27
    3ad2ant1
    #
    @23
    @30
    @1
    @53
    @28
    3ad2ant1
    @23
    @30
    @53
    simp2
    @23
    @30
    @22
    @53
    @29
    3ad2ant1
    @23
    @30
    @53
    simp3
    @26
    uvcvv0
    oveq2d
    @54
    @0
    @41
    @55
    @25
    wceq
    @56
    @23
    @30
    @41
    @53
    @3
    @30
    @41
    @22
    @37
    adantlr
    3adant3
    @19
    cR
    @9
    @5
    @25
    @20
    @40
    @26
    ringrz
    syl2anc
    eqtrd
    @28
    suppsssn
    gsumpt
    @23
    @24
    @18
    @6
    @6
    cU
    cfv
    #
    cfv
    #
    @9
    co
    #
    @18
    @22
    @24
    @59
    wceq
    @3
    vb
    @6
    @10
    @59
    cI
    @15
    @4
    @6
    wceq
    #
    @5
    @18
    @8
    @58
    @9
    @4
    @6
    cX
    fveq2
    @60
    @6
    @7
    @57
    @4
    @6
    cU
    fveq2
    fveq1d
    oveq12d
    @52
    @18
    @58
    @9
    ovex
    fvmpt
    adantl
    @23
    @59
    @18
    cR
    cur
    cfv
    #
    @9
    co
    #
    @18
    @23
    @58
    @61
    @18
    @9
    @23
    cR
    cU
    @61
    cI
    @6
    crg
    cW
    uvcresum.u
    @27
    @28
    @29
    @61
    eqid
    #
    uvcvv1
    oveq2d
    @23
    @0
    @18
    @19
    wcel
    @62
    @18
    wceq
    @27
    @3
    cI
    @19
    @6
    cX
    @21
    ffvelrnda
    @19
    cR
    @9
    @61
    @18
    @20
    @40
    @63
    ringridm
    syl2anc
    eqtrd
    eqtrd
    eqtrd
    mpteq2dva
    eqtr4d
    @3
    va
    vb
    cB
    cR
    @10
    cI
    cI
    cW
    cW
    cY
    cY
    c0g
    cfv
    #
    uvcresum.y
    uvcresum.b
    @64
    eqid
    #
    @0
    @1
    @2
    simp2
    #
    @66
    @0
    @1
    @2
    simp1
    @51
    @3
    @12
    cvv
    wcel
    #
    @12
    wfun
    #
    @64
    cvv
    wcel
    cX
    @25
    csupp
    co
    #
    cfn
    wcel
    @12
    @64
    csupp
    co
    @69
    wss
    @12
    @64
    cfsupp
    wbr
    @1
    @0
    @67
    @2
    vb
    cI
    @11
    cW
    mptexg
    3ad2ant2
    @68
    @3
    vb
    cI
    @11
    funmpt
    a1i
    @3
    cY
    c0g
    fvexd
    @3
    cX
    @25
    @1
    @2
    cX
    @25
    cfsupp
    wbr
    @0
    cB
    cR
    cY
    cI
    cW
    cX
    @25
    uvcresum.y
    @26
    uvcresum.b
    frlmbasfsupp
    3adant1
    fsuppimpd
    @3
    cI
    @11
    vb
    cW
    @69
    @64
    @3
    @4
    cI
    @69
    cdif
    wcel
    #
    wa
    #
    @35
    @46
    c0g
    cfv
    #
    @7
    c.x
    co
    #
    @11
    @64
    @71
    @5
    @72
    @7
    c.x
    @3
    cI
    @19
    cvv
    cX
    cW
    @69
    @4
    @72
    @21
    @3
    cX
    @72
    csupp
    co
    @69
    @69
    @3
    @72
    @25
    cX
    csupp
    @3
    @46
    cR
    c0g
    @3
    cR
    @46
    @49
    eqcomd
    fveq2d
    oveq2d
    @69
    ssid
    syl6eqss
    @66
    @3
    @46
    c0g
    fvexd
    suppssr
    oveq1d
    @70
    @3
    @30
    @35
    @11
    wceq
    @4
    cI
    @69
    eldifi
    #
    @44
    sylan2
    @71
    @45
    @42
    @73
    @64
    wceq
    @3
    @45
    @70
    @48
    adantr
    @70
    @3
    @30
    @42
    @74
    @39
    sylan2
    c.x
    @46
    @72
    cB
    cY
    @7
    @64
    uvcresum.b
    @50
    uvcresum.v
    @72
    eqid
    @65
    lmod0vs
    syl2anc
    3eqtr3d
    @66
    suppss2
    @69
    @12
    cvv
    cvv
    @64
    suppssfifsupp
    syl32anc
    frlmgsum
    eqtr4d
    @3
    @14
    @12
    cY
    cgsu
    @3
    @14
    vb
    cI
    @35
    cmpt
    @12
    @3
    vb
    cI
    @5
    @7
    c.x
    cX
    cU
    cW
    @19
    cB
    @66
    @37
    @39
    @3
    vb
    cI
    @19
    cX
    @21
    feqmptd
    @3
    vb
    cI
    cB
    cU
    @38
    feqmptd
    offval2
    @3
    vb
    cI
    @35
    @11
    @44
    mpteq2dva
    eqtrd
    oveq2d
    eqtr4d
end
