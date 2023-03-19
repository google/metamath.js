include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wrex.mm"
include "csn.mm"
include "cun.mm"
include "clmod.mm"
include "wss.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "wa.mm"
include "c0g.mm"
include "adantr.mm"
include "eqid.mm"
include "lmod0cl.mm"
include "syl.mm"
include "wceq.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "sselda.mm"
include "lmod0vrid.mm"
include "eqtrd.mm"
include "lspssid.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "ssrabdv.mm"
include "syl6sseqr.mm"
include "cur.mm"
include "cminusg.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "lmod1cl.mm"
include "grpinvcl.mm"
include "lmodvneg1.mm"
include "lmodgrp.mm"
include "grprinv.mm"
include "lspcl.mm"
include "lss0cl.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "unssd.mm"
include "lspss.mm"
include "syl3anc.mm"
include "csca.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvsca.mm"
include "clss.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "weq.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitri.mm"
include "reeanv.mm"
include "w3a.mm"
include "simp1ll.mm"
include "simp1lr.mm"
include "simp1rl.mm"
include "lmodvscl.mm"
include "simp1rr.mm"
include "lmodvacl.mm"
include "cmulr.mm"
include "simp2l.mm"
include "lmodmcl.mm"
include "simp2r.mm"
include "lmodacl.mm"
include "lmod4.mm"
include "syl122anc.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "lmodvsass.mm"
include "oveq1d.mm"
include "lmodvsdi.mm"
include "3eqtr4d.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lsscl.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "exp4b.mm"
include "3imp2.mm"
include "islssd.mm"
include "lspid.mm"
include "sseqtrd.mm"
include "sseldd.mm"
include "simprbi.mm"

theorem lspsolvlem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cQ: class Q
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  assume lspsolv.v: |- V = ( Base ` W )
  assume lspsolv.s: |- S = ( LSubSp ` W )
  assume lspsolv.n: |- N = ( LSpan ` W )
  assume lspsolv.f: |- F = ( Scalar ` W )
  assume lspsolv.b: |- B = ( Base ` F )
  assume lspsolv.p: |- .+ = ( +g ` W )
  assume lspsolv.t: |- .x. = ( .s ` W )
  assume lspsolv.q: |- Q = { z e. V | E. r e. B ( z .+ ( r .x. Y ) ) e. ( N ` A ) }
  assume lspsolv.w: |- ( ph -> W e. LMod )
  assume lspsolv.ss: |- ( ph -> A C_ V )
  assume lspsolv.y: |- ( ph -> Y e. V )
  assume lspsolv.x: |- ( ph -> X e. ( N ` ( A u. { Y } ) ) )

  disjoint r z
  disjoint A r
  disjoint A z
  disjoint B r
  disjoint B z
  disjoint N r
  disjoint N z
  disjoint ph z
  disjoint F r
  disjoint S r
  disjoint V r
  disjoint V z
  disjoint W r
  disjoint W z
  disjoint .+ r
  disjoint .+ z
  disjoint .x. r
  disjoint .x. z
  disjoint X r
  disjoint X z
  disjoint Y r
  disjoint Y z
  disjoint r s
  disjoint r t
  disjoint s t
  disjoint s z
  disjoint A s
  disjoint t z
  disjoint A t
  disjoint r x
  disjoint r y
  disjoint s x
  disjoint s y
  disjoint B s
  disjoint t x
  disjoint t y
  disjoint B t
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint N s
  disjoint N t
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint ph s
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint Q a
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint V s
  disjoint V t
  disjoint a r
  disjoint W a
  disjoint W x
  disjoint W y
  disjoint .+ s
  disjoint .+ t
  disjoint .x. s
  disjoint .x. t
  disjoint Y s
  disjoint Y t
  assert |- ( ph -> E. r e. B ( X .+ ( r .x. Y ) ) e. ( N ` A ) )

  proof
    wph
    cX
    cQ
    wcel
    #
    cX
    vr
    cv
    #
    cY
    c.x
    co
    #
    c.pl
    co
    #
    cA
    cN
    cfv
    #
    wcel
    #
    vr
    cB
    wrex
    #
    wph
    cA
    cY
    csn
    #
    cun
    #
    cN
    cfv
    #
    cQ
    cX
    wph
    @9
    cQ
    cN
    cfv
    #
    cQ
    wph
    cW
    clmod
    wcel
    #
    cQ
    cV
    wss
    #
    @8
    cQ
    wss
    @9
    @10
    wss
    lspsolv.w
    @12
    wph
    cQ
    vz
    cv
    #
    @2
    c.pl
    co
    #
    @4
    wcel
    #
    vr
    cB
    wrex
    #
    vz
    cV
    crab
    #
    cV
    lspsolv.q
    @16
    vz
    cV
    ssrab2
    eqsstri
    a1i
    #
    wph
    cA
    @7
    cQ
    wph
    cA
    @17
    cQ
    wph
    @16
    vz
    cV
    cA
    lspsolv.ss
    wph
    @13
    cA
    wcel
    #
    wa
    #
    cF
    c0g
    cfv
    #
    cB
    wcel
    #
    @13
    @21
    cY
    c.x
    co
    #
    c.pl
    co
    #
    @4
    wcel
    #
    @16
    @20
    @11
    @22
    wph
    @11
    @19
    lspsolv.w
    adantr
    #
    cF
    cB
    cW
    @21
    lspsolv.f
    lspsolv.b
    @21
    eqid
    #
    lmod0cl
    syl
    @20
    @24
    @13
    @4
    @20
    @24
    @13
    cW
    c0g
    cfv
    #
    c.pl
    co
    #
    @13
    @20
    @23
    @28
    @13
    c.pl
    wph
    @23
    @28
    wceq
    #
    @19
    wph
    @11
    cY
    cV
    wcel
    #
    @30
    lspsolv.w
    lspsolv.y
    c.x
    cF
    @21
    cV
    cW
    cY
    @28
    lspsolv.v
    lspsolv.f
    lspsolv.t
    @27
    @28
    eqid
    #
    lmod0vs
    syl2anc
    adantr
    oveq2d
    @20
    @11
    @13
    cV
    wcel
    @29
    @13
    wceq
    @26
    wph
    cA
    cV
    @13
    lspsolv.ss
    sselda
    c.pl
    cV
    cW
    @13
    @28
    lspsolv.v
    lspsolv.p
    @32
    lmod0vrid
    syl2anc
    eqtrd
    wph
    cA
    @4
    @13
    wph
    @11
    cA
    cV
    wss
    #
    cA
    @4
    wss
    lspsolv.w
    lspsolv.ss
    cA
    cN
    cV
    cW
    lspsolv.v
    lspsolv.n
    lspssid
    syl2anc
    sselda
    eqeltrd
    @15
    @25
    vr
    @21
    cB
    @1
    @21
    wceq
    #
    @14
    @24
    @4
    @34
    @2
    @23
    @13
    c.pl
    @1
    @21
    cY
    c.x
    oveq1
    oveq2d
    eleq1d
    rspcev
    syl2anc
    ssrabdv
    lspsolv.q
    syl6sseqr
    wph
    cY
    cQ
    wph
    @31
    cY
    @2
    c.pl
    co
    #
    @4
    wcel
    #
    vr
    cB
    wrex
    #
    cY
    cQ
    wcel
    #
    lspsolv.y
    wph
    cF
    cur
    cfv
    #
    cF
    cminusg
    cfv
    #
    cfv
    #
    cB
    wcel
    #
    cY
    @41
    cY
    c.x
    co
    #
    c.pl
    co
    #
    @4
    wcel
    #
    @37
    wph
    cF
    cgrp
    wcel
    #
    @39
    cB
    wcel
    #
    @42
    wph
    @11
    @46
    lspsolv.w
    cF
    cW
    lspsolv.f
    lmodfgrp
    syl
    wph
    @11
    @47
    lspsolv.w
    @39
    cF
    cB
    cW
    lspsolv.f
    lspsolv.b
    @39
    eqid
    #
    lmod1cl
    syl
    cB
    cF
    @40
    @39
    lspsolv.b
    @40
    eqid
    #
    grpinvcl
    syl2anc
    wph
    @44
    @28
    @4
    wph
    @44
    cY
    cY
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    @28
    wph
    @43
    @51
    cY
    c.pl
    wph
    @11
    @31
    @43
    @51
    wceq
    lspsolv.w
    lspsolv.y
    c.x
    @39
    cF
    @40
    @50
    cV
    cW
    cY
    lspsolv.v
    @50
    eqid
    #
    lspsolv.f
    lspsolv.t
    @48
    @49
    lmodvneg1
    syl2anc
    oveq2d
    wph
    cW
    cgrp
    wcel
    #
    @31
    @52
    @28
    wceq
    wph
    @11
    @54
    lspsolv.w
    cW
    lmodgrp
    syl
    lspsolv.y
    cV
    c.pl
    cW
    @50
    cY
    @28
    lspsolv.v
    lspsolv.p
    @32
    @53
    grprinv
    syl2anc
    eqtrd
    wph
    @11
    @4
    cS
    wcel
    #
    @28
    @4
    wcel
    lspsolv.w
    wph
    @11
    @33
    @55
    lspsolv.w
    lspsolv.ss
    cS
    cA
    cN
    cV
    cW
    lspsolv.v
    lspsolv.s
    lspsolv.n
    lspcl
    syl2anc
    #
    cS
    @4
    cW
    @28
    @32
    lspsolv.s
    lss0cl
    syl2anc
    eqeltrd
    @36
    @45
    vr
    @41
    cB
    @1
    @41
    wceq
    #
    @35
    @44
    @4
    @57
    @2
    @43
    cY
    c.pl
    @1
    @41
    cY
    c.x
    oveq1
    oveq2d
    eleq1d
    rspcev
    syl2anc
    @16
    @37
    vz
    cY
    cV
    cQ
    @13
    cY
    wceq
    #
    @15
    @36
    vr
    cB
    @58
    @14
    @35
    @4
    @13
    cY
    @2
    c.pl
    oveq1
    eleq1d
    rexbidv
    lspsolv.q
    elrab2
    sylanbrc
    #
    snssd
    unssd
    @8
    cQ
    cN
    cV
    cW
    lspsolv.v
    lspsolv.n
    lspss
    syl3anc
    wph
    @11
    cQ
    cS
    wcel
    @10
    cQ
    wceq
    lspsolv.w
    wph
    va
    cB
    c.pl
    cS
    c.x
    cQ
    cF
    cV
    cW
    vx
    vy
    cF
    cW
    csca
    cfv
    wceq
    wph
    lspsolv.f
    a1i
    cB
    cF
    cbs
    cfv
    wceq
    wph
    lspsolv.b
    a1i
    cV
    cW
    cbs
    cfv
    wceq
    wph
    lspsolv.v
    a1i
    c.pl
    cW
    cplusg
    cfv
    wceq
    wph
    lspsolv.p
    a1i
    c.x
    cW
    cvsca
    cfv
    wceq
    wph
    lspsolv.t
    a1i
    cS
    cW
    clss
    cfv
    wceq
    wph
    lspsolv.s
    a1i
    @18
    wph
    @38
    cQ
    c0
    wne
    @59
    cQ
    cY
    ne0i
    syl
    wph
    va
    cv
    #
    cB
    wcel
    #
    vx
    cv
    #
    cQ
    wcel
    #
    vy
    cv
    #
    cQ
    wcel
    #
    @60
    @62
    c.x
    co
    #
    @64
    c.pl
    co
    #
    cQ
    wcel
    #
    wph
    @61
    @63
    @65
    @68
    @63
    @65
    wa
    #
    @62
    cV
    wcel
    #
    @64
    cV
    wcel
    #
    wa
    #
    @62
    vs
    cv
    #
    cY
    c.x
    co
    #
    c.pl
    co
    #
    @4
    wcel
    #
    vs
    cB
    wrex
    #
    @64
    vt
    cv
    #
    cY
    c.x
    co
    #
    c.pl
    co
    #
    @4
    wcel
    #
    vt
    cB
    wrex
    #
    wa
    #
    wa
    #
    wph
    @61
    wa
    #
    @68
    @69
    @70
    @77
    wa
    #
    @71
    @82
    wa
    #
    wa
    @84
    @63
    @86
    @65
    @87
    @16
    @77
    vz
    @62
    cV
    cQ
    vz
    vx
    weq
    #
    @16
    @62
    @2
    c.pl
    co
    #
    @4
    wcel
    #
    vr
    cB
    wrex
    @77
    @88
    @15
    @90
    vr
    cB
    @88
    @14
    @89
    @4
    @13
    @62
    @2
    c.pl
    oveq1
    eleq1d
    rexbidv
    @90
    @76
    vr
    vs
    cB
    vr
    vs
    weq
    #
    @89
    @75
    @4
    @91
    @2
    @74
    @62
    c.pl
    @1
    @73
    cY
    c.x
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    syl6bb
    lspsolv.q
    elrab2
    @16
    @82
    vz
    @64
    cV
    cQ
    vz
    vy
    weq
    #
    @16
    @64
    @2
    c.pl
    co
    #
    @4
    wcel
    #
    vr
    cB
    wrex
    @82
    @92
    @15
    @94
    vr
    cB
    @92
    @14
    @93
    @4
    @13
    @64
    @2
    c.pl
    oveq1
    eleq1d
    rexbidv
    @94
    @81
    vr
    vt
    cB
    vr
    vt
    weq
    #
    @93
    @80
    @4
    @95
    @2
    @79
    @64
    c.pl
    @1
    @78
    cY
    c.x
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    syl6bb
    lspsolv.q
    elrab2
    anbi12i
    @70
    @77
    @71
    @82
    an4
    bitri
    @85
    @72
    @83
    @68
    @83
    @76
    @81
    wa
    #
    vt
    cB
    wrex
    vs
    cB
    wrex
    @85
    @72
    wa
    #
    @68
    @76
    @81
    vs
    vt
    cB
    cB
    reeanv
    @97
    @96
    @68
    vs
    vt
    cB
    cB
    @97
    @73
    cB
    wcel
    #
    @78
    cB
    wcel
    #
    wa
    #
    @96
    @68
    @97
    @100
    @96
    w3a
    #
    @67
    cV
    wcel
    #
    @67
    @2
    c.pl
    co
    #
    @4
    wcel
    #
    vr
    cB
    wrex
    #
    @68
    @101
    @11
    @66
    cV
    wcel
    #
    @71
    @102
    @101
    wph
    @11
    wph
    @61
    @72
    @100
    @96
    simp1ll
    #
    lspsolv.w
    syl
    #
    @101
    @11
    @61
    @70
    @106
    @108
    wph
    @61
    @72
    @100
    @96
    simp1lr
    #
    @70
    @71
    @85
    @100
    @96
    simp1rl
    #
    @60
    c.x
    cF
    cB
    cV
    cW
    @62
    lspsolv.v
    lspsolv.f
    lspsolv.t
    lspsolv.b
    lmodvscl
    syl3anc
    #
    @70
    @71
    @85
    @100
    @96
    simp1rr
    #
    c.pl
    cV
    cW
    @66
    @64
    lspsolv.v
    lspsolv.p
    lmodvacl
    syl3anc
    @101
    @60
    @73
    cF
    cmulr
    cfv
    #
    co
    #
    @78
    cF
    cplusg
    cfv
    #
    co
    #
    cB
    wcel
    #
    @67
    @116
    cY
    c.x
    co
    #
    c.pl
    co
    #
    @4
    wcel
    #
    @105
    @101
    @11
    @114
    cB
    wcel
    #
    @99
    @117
    @108
    @101
    @11
    @61
    @98
    @121
    @108
    @109
    @97
    @98
    @99
    @96
    simp2l
    #
    @113
    cF
    cB
    cW
    @60
    @73
    lspsolv.f
    lspsolv.b
    @113
    eqid
    #
    lmodmcl
    syl3anc
    #
    @97
    @98
    @99
    @96
    simp2r
    #
    @115
    cF
    cB
    cW
    @114
    @78
    lspsolv.f
    lspsolv.b
    @115
    eqid
    #
    lmodacl
    syl3anc
    @101
    @119
    @60
    @75
    c.x
    co
    #
    @80
    c.pl
    co
    #
    @4
    @101
    @67
    @60
    @74
    c.x
    co
    #
    @79
    c.pl
    co
    #
    c.pl
    co
    #
    @66
    @129
    c.pl
    co
    #
    @80
    c.pl
    co
    #
    @119
    @128
    @101
    @11
    @106
    @71
    @129
    cV
    wcel
    #
    @79
    cV
    wcel
    #
    @131
    @133
    wceq
    @108
    @111
    @112
    @101
    @11
    @61
    @74
    cV
    wcel
    #
    @134
    @108
    @109
    @101
    @11
    @98
    @31
    @136
    @108
    @122
    @101
    wph
    @31
    @107
    lspsolv.y
    syl
    #
    @73
    c.x
    cF
    cB
    cV
    cW
    cY
    lspsolv.v
    lspsolv.f
    lspsolv.t
    lspsolv.b
    lmodvscl
    syl3anc
    #
    @60
    c.x
    cF
    cB
    cV
    cW
    @74
    lspsolv.v
    lspsolv.f
    lspsolv.t
    lspsolv.b
    lmodvscl
    syl3anc
    @101
    @11
    @99
    @31
    @135
    @108
    @125
    @137
    @78
    c.x
    cF
    cB
    cV
    cW
    cY
    lspsolv.v
    lspsolv.f
    lspsolv.t
    lspsolv.b
    lmodvscl
    syl3anc
    c.pl
    @79
    cV
    cW
    @66
    @64
    @129
    lspsolv.v
    lspsolv.p
    lmod4
    syl122anc
    @101
    @118
    @130
    @67
    c.pl
    @101
    @118
    @114
    cY
    c.x
    co
    #
    @79
    c.pl
    co
    #
    @130
    @101
    @11
    @121
    @99
    @31
    @118
    @140
    wceq
    @108
    @124
    @125
    @137
    c.pl
    @115
    @114
    @78
    c.x
    cF
    cB
    cV
    cW
    cY
    lspsolv.v
    lspsolv.p
    lspsolv.f
    lspsolv.t
    lspsolv.b
    @126
    lmodvsdir
    syl13anc
    @101
    @139
    @129
    @79
    c.pl
    @101
    @11
    @61
    @98
    @31
    @139
    @129
    wceq
    @108
    @109
    @122
    @137
    @60
    @73
    c.x
    @113
    cF
    cB
    cV
    cW
    cY
    lspsolv.v
    lspsolv.f
    lspsolv.t
    lspsolv.b
    @123
    lmodvsass
    syl13anc
    oveq1d
    eqtrd
    oveq2d
    @101
    @127
    @132
    @80
    c.pl
    @101
    @11
    @61
    @70
    @136
    @127
    @132
    wceq
    @108
    @109
    @110
    @138
    c.pl
    @60
    c.x
    cF
    cB
    cV
    cW
    @62
    @74
    lspsolv.v
    lspsolv.p
    lspsolv.f
    lspsolv.t
    lspsolv.b
    lmodvsdi
    syl13anc
    oveq1d
    3eqtr4d
    @101
    @55
    @61
    @76
    @81
    @128
    @4
    wcel
    @101
    wph
    @55
    @107
    @56
    syl
    @109
    @97
    @100
    @76
    @81
    simp3l
    @97
    @100
    @76
    @81
    simp3r
    cB
    c.pl
    cS
    c.x
    @4
    cF
    cW
    @75
    @80
    @60
    lspsolv.f
    lspsolv.b
    lspsolv.p
    lspsolv.t
    lspsolv.s
    lsscl
    syl13anc
    eqeltrd
    @104
    @120
    vr
    @116
    cB
    @1
    @116
    wceq
    #
    @103
    @119
    @4
    @141
    @2
    @118
    @67
    c.pl
    @1
    @116
    cY
    c.x
    oveq1
    oveq2d
    eleq1d
    rspcev
    syl2anc
    @16
    @105
    vz
    @67
    cV
    cQ
    @13
    @67
    wceq
    #
    @15
    @104
    vr
    cB
    @142
    @14
    @103
    @4
    @13
    @67
    @2
    c.pl
    oveq1
    eleq1d
    rexbidv
    lspsolv.q
    elrab2
    sylanbrc
    3exp
    rexlimdvv
    syl5bir
    expimpd
    syl5bi
    exp4b
    3imp2
    islssd
    cS
    cQ
    cN
    cW
    lspsolv.s
    lspsolv.n
    lspid
    syl2anc
    sseqtrd
    lspsolv.x
    sseldd
    @0
    cX
    cV
    wcel
    @6
    @16
    @6
    vz
    cX
    cV
    cQ
    @13
    cX
    wceq
    #
    @15
    @5
    vr
    cB
    @143
    @14
    @3
    @4
    @13
    cX
    @2
    c.pl
    oveq1
    eleq1d
    rexbidv
    lspsolv.q
    elrab2
    simprbi
    syl
end
