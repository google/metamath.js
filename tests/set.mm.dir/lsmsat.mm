include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cdif.mm"
include "wrex.mm"
include "wss.mm"
include "co.mm"
include "wa.mm"
include "wcel.mm"
include "clmod.mm"
include "wb.mm"
include "eqid.mm"
include "islsat.mm"
include "syl.mm"
include "mpbid.mm"
include "w3a.mm"
include "cplusg.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "eqsstr3d.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "eldifi.mm"
include "3ad2ant2.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsmelval.mm"
include "syl2anc.mm"
include "wi.mm"
include "wne.mm"
include "lssne0.mm"
include "adantr.mm"
include "simpr2.mm"
include "lssel.mm"
include "simpr3.mm"
include "lsatlspsn2.mm"
include "lspsnel5a.mm"
include "simpl3.mm"
include "simpr1.mm"
include "oveq1d.mm"
include "simp2r.mm"
include "lmod0vlid.mm"
include "3eqtrd.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqsstrd.mm"
include "lspsnsubg.mm"
include "lsmub2.mm"
include "sstrd.mm"
include "sseq1.mm"
include "oveq1.mm"
include "sseq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "3exp2.mm"
include "imp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "simp2l.mm"
include "simpr.mm"
include "cpr.mm"
include "lspvadd.mm"
include "lsmpr.mm"
include "sseqtrd.mm"
include "lspsncl.mm"
include "lsmless2.mm"
include "pm2.61dane.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "3adant3.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "3ad2ant3.mm"

theorem lsmsat
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let c.0: class .0.
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  assume lsmsat.o: |- .0. = ( 0g ` W )
  assume lsmsat.s: |- S = ( LSubSp ` W )
  assume lsmsat.p: |- .(+) = ( LSSum ` W )
  assume lsmsat.a: |- A = ( LSAtoms ` W )
  assume lsmsat.w: |- ( ph -> W e. LMod )
  assume lsmsat.t: |- ( ph -> T e. S )
  assume lsmsat.u: |- ( ph -> U e. S )
  assume lsmsat.q: |- ( ph -> Q e. A )
  assume lsmsat.n: |- ( ph -> T =/= { .0. } )
  assume lsmsat.l: |- ( ph -> Q C_ ( T .(+) U ) )

  disjoint A p
  disjoint .(+) p
  disjoint Q p
  disjoint T p
  disjoint U p
  disjoint W p
  disjoint p q
  disjoint p r
  disjoint p y
  disjoint p z
  disjoint q r
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint .0. q
  disjoint .0. r
  disjoint .0. y
  disjoint .0. z
  disjoint .(+) q
  disjoint .(+) r
  disjoint .(+) y
  disjoint .(+) z
  disjoint Q r
  disjoint T q
  disjoint T r
  disjoint T y
  disjoint T z
  disjoint U q
  disjoint U r
  disjoint U y
  disjoint U z
  disjoint W q
  disjoint W r
  disjoint W y
  disjoint W z
  disjoint ph q
  disjoint ph r
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> E. p e. A ( p C_ T /\ Q C_ ( p .(+) U ) ) )

  proof
    wph
    cQ
    vr
    cv
    #
    csn
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vr
    cW
    cbs
    cfv
    #
    c.0
    csn
    #
    cdif
    #
    wrex
    #
    vp
    cv
    #
    cT
    wss
    #
    cQ
    @9
    cU
    c.po
    co
    #
    wss
    #
    wa
    #
    vp
    cA
    wrex
    #
    wph
    cQ
    cA
    wcel
    #
    @8
    lsmsat.q
    wph
    cW
    clmod
    wcel
    #
    @15
    @8
    wb
    lsmsat.w
    vr
    cA
    cQ
    @2
    @5
    cW
    clmod
    c.0
    @5
    eqid
    #
    @2
    eqid
    #
    lsmsat.o
    lsmsat.a
    islsat
    syl
    mpbid
    wph
    @4
    @14
    vr
    @7
    wph
    @0
    @7
    wcel
    #
    @4
    @14
    wph
    @19
    @4
    w3a
    #
    @14
    @10
    @3
    @11
    wss
    #
    wa
    #
    vp
    cA
    wrex
    #
    @20
    @0
    vy
    cv
    #
    vz
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    cU
    wrex
    vy
    cT
    wrex
    #
    @23
    @20
    @0
    cT
    cU
    c.po
    co
    #
    wcel
    #
    @29
    @20
    @31
    @3
    @30
    wss
    @20
    @3
    cQ
    @30
    wph
    @19
    @4
    simp3
    wph
    @19
    cQ
    @30
    wss
    @4
    lsmsat.l
    3ad2ant1
    eqsstr3d
    @20
    cS
    @30
    @2
    @5
    cW
    @0
    @17
    lsmsat.s
    @18
    wph
    @19
    @16
    @4
    lsmsat.w
    3ad2ant1
    #
    wph
    @19
    @30
    cS
    wcel
    #
    @4
    wph
    @16
    cT
    cS
    wcel
    #
    cU
    cS
    wcel
    #
    @33
    lsmsat.w
    lsmsat.t
    lsmsat.u
    c.po
    cS
    cT
    cU
    cW
    lsmsat.s
    lsmsat.p
    lsmcl
    syl3anc
    3ad2ant1
    @19
    wph
    @0
    @5
    wcel
    @4
    @0
    @5
    @6
    eldifi
    3ad2ant2
    lspsnel5
    mpbird
    @20
    cT
    cW
    csubg
    cfv
    #
    wcel
    cU
    @36
    wcel
    #
    @31
    @29
    wb
    @20
    cS
    @36
    cT
    @20
    @16
    cS
    @36
    wss
    #
    @32
    cS
    cW
    lsmsat.s
    lsssssubg
    #
    syl
    #
    wph
    @19
    @34
    @4
    lsmsat.t
    3ad2ant1
    sseldd
    @20
    cS
    @36
    cU
    @40
    wph
    @19
    @35
    @4
    lsmsat.u
    3ad2ant1
    sseldd
    vy
    vz
    @26
    c.po
    cT
    cU
    cW
    @0
    @26
    eqid
    #
    lsmsat.p
    lsmelval
    syl2anc
    mpbid
    wph
    @19
    @29
    @23
    wi
    @4
    wph
    @19
    wa
    #
    @28
    @23
    vy
    vz
    cT
    cU
    @42
    @24
    cT
    wcel
    #
    @25
    cU
    wcel
    #
    wa
    #
    @28
    @23
    @42
    @45
    @28
    w3a
    #
    @23
    @24
    c.0
    @46
    @24
    c.0
    wceq
    #
    wa
    #
    vq
    cv
    #
    c.0
    wne
    #
    vq
    cT
    wrex
    #
    @23
    @46
    @51
    @47
    @42
    @45
    @51
    @28
    wph
    @51
    @19
    wph
    cT
    @6
    wne
    #
    @51
    lsmsat.n
    wph
    @34
    @52
    @51
    wb
    lsmsat.t
    vq
    cS
    cW
    cT
    c.0
    lsmsat.o
    lsmsat.s
    lssne0
    syl
    mpbid
    adantr
    3ad2ant1
    adantr
    @48
    @50
    @23
    vq
    cT
    @46
    @47
    @49
    cT
    wcel
    #
    @50
    @23
    wi
    wi
    @46
    @47
    @53
    @50
    @23
    @46
    @47
    @53
    @50
    w3a
    #
    wa
    #
    @49
    csn
    @2
    cfv
    #
    cA
    wcel
    #
    @56
    cT
    wss
    #
    @3
    @56
    cU
    c.po
    co
    #
    wss
    #
    @23
    @55
    @16
    @49
    @5
    wcel
    #
    @50
    @57
    @46
    @16
    @54
    @42
    @45
    @16
    @28
    wph
    @16
    @19
    lsmsat.w
    adantr
    3ad2ant1
    #
    adantr
    #
    @55
    @34
    @53
    @61
    @46
    @34
    @54
    @42
    @45
    @34
    @28
    wph
    @34
    @19
    lsmsat.t
    adantr
    3ad2ant1
    #
    adantr
    #
    @46
    @47
    @53
    @50
    simpr2
    #
    cS
    cT
    @5
    cW
    @49
    @17
    lsmsat.s
    lssel
    syl2anc
    #
    @46
    @47
    @53
    @50
    simpr3
    cA
    @2
    @5
    cW
    @49
    c.0
    @17
    @18
    lsmsat.o
    lsmsat.a
    lsatlspsn2
    syl3anc
    @55
    cS
    cT
    @2
    cW
    @49
    lsmsat.s
    @18
    @63
    @65
    @66
    lspsnel5a
    @55
    @3
    cU
    @59
    @55
    @3
    @25
    csn
    #
    @2
    cfv
    #
    cU
    @55
    @1
    @68
    @2
    @55
    @0
    @25
    @55
    @0
    @27
    c.0
    @25
    @26
    co
    #
    @25
    @42
    @45
    @28
    @54
    simpl3
    @55
    @24
    c.0
    @25
    @26
    @46
    @47
    @53
    @50
    simpr1
    oveq1d
    @55
    @16
    @25
    @5
    wcel
    #
    @70
    @25
    wceq
    @63
    @46
    @71
    @54
    @46
    @35
    @44
    @71
    @42
    @45
    @35
    @28
    wph
    @35
    @19
    lsmsat.u
    adantr
    3ad2ant1
    #
    @42
    @43
    @44
    @28
    simp2r
    #
    cS
    cU
    @5
    cW
    @25
    @17
    lsmsat.s
    lssel
    syl2anc
    #
    adantr
    @26
    @5
    cW
    @25
    c.0
    @17
    @41
    lsmsat.o
    lmod0vlid
    syl2anc
    3eqtrd
    sneqd
    fveq2d
    @46
    @69
    cU
    wss
    #
    @54
    @46
    cS
    cU
    @2
    cW
    @25
    lsmsat.s
    @18
    @62
    @72
    @73
    lspsnel5a
    #
    adantr
    eqsstrd
    @55
    @56
    @36
    wcel
    #
    @37
    cU
    @59
    wss
    @55
    @16
    @61
    @77
    @63
    @67
    @2
    @5
    cW
    @49
    @17
    @18
    lspsnsubg
    syl2anc
    @55
    cS
    @36
    cU
    @55
    @16
    @38
    @63
    @39
    syl
    @46
    @35
    @54
    @72
    adantr
    sseldd
    c.po
    @56
    cU
    cW
    lsmsat.p
    lsmub2
    syl2anc
    sstrd
    @22
    @58
    @60
    wa
    vp
    @56
    cA
    @9
    @56
    wceq
    #
    @10
    @58
    @21
    @60
    @9
    @56
    cT
    sseq1
    @78
    @11
    @59
    @3
    @9
    @56
    cU
    c.po
    oveq1
    sseq2d
    anbi12d
    rspcev
    syl12anc
    3exp2
    imp
    rexlimdv
    mpd
    @46
    @24
    c.0
    wne
    #
    wa
    #
    @24
    csn
    @2
    cfv
    #
    cA
    wcel
    #
    @81
    cT
    wss
    #
    @3
    @81
    cU
    c.po
    co
    #
    wss
    #
    @23
    @80
    @16
    @24
    @5
    wcel
    #
    @79
    @82
    @46
    @16
    @79
    @62
    adantr
    @46
    @86
    @79
    @46
    @34
    @43
    @86
    @64
    @42
    @43
    @44
    @28
    simp2l
    #
    cS
    cT
    @5
    cW
    @24
    @17
    lsmsat.s
    lssel
    syl2anc
    #
    adantr
    @46
    @79
    simpr
    cA
    @2
    @5
    cW
    @24
    c.0
    @17
    @18
    lsmsat.o
    lsmsat.a
    lsatlspsn2
    syl3anc
    @46
    @83
    @79
    @46
    cS
    cT
    @2
    cW
    @24
    lsmsat.s
    @18
    @62
    @64
    @87
    lspsnel5a
    adantr
    @46
    @85
    @79
    @46
    @3
    @81
    @69
    c.po
    co
    #
    @84
    @46
    @3
    @24
    @25
    cpr
    @2
    cfv
    #
    @89
    @46
    @3
    @27
    csn
    #
    @2
    cfv
    #
    @90
    @46
    @1
    @91
    @2
    @46
    @0
    @27
    @42
    @45
    @28
    simp3
    sneqd
    fveq2d
    @46
    @16
    @86
    @71
    @92
    @90
    wss
    @62
    @88
    @74
    @26
    @2
    @5
    cW
    @24
    @25
    @17
    @41
    @18
    lspvadd
    syl3anc
    eqsstrd
    @46
    c.po
    @2
    @5
    cW
    @24
    @25
    @17
    @18
    lsmsat.p
    @62
    @88
    @74
    lsmpr
    sseqtrd
    @46
    @81
    @36
    wcel
    @37
    @75
    @89
    @84
    wss
    @46
    cS
    @36
    @81
    @46
    @16
    @38
    @62
    @39
    syl
    #
    @46
    @16
    @86
    @81
    cS
    wcel
    @62
    @88
    cS
    @2
    @5
    cW
    @24
    @17
    lsmsat.s
    @18
    lspsncl
    syl2anc
    sseldd
    @46
    cS
    @36
    cU
    @93
    @72
    sseldd
    @76
    c.po
    @81
    @69
    cU
    cW
    lsmsat.p
    lsmless2
    syl3anc
    sstrd
    adantr
    @22
    @83
    @85
    wa
    vp
    @81
    cA
    @9
    @81
    wceq
    #
    @10
    @83
    @21
    @85
    @9
    @81
    cT
    sseq1
    @94
    @11
    @84
    @3
    @9
    @81
    cU
    c.po
    oveq1
    sseq2d
    anbi12d
    rspcev
    syl12anc
    pm2.61dane
    3exp
    rexlimdvv
    3adant3
    mpd
    @4
    wph
    @14
    @23
    wb
    @19
    @4
    @13
    @22
    vp
    cA
    @4
    @12
    @21
    @10
    cQ
    @3
    @11
    sseq1
    anbi2d
    rexbidv
    3ad2ant3
    mpbird
    3exp
    rexlimdv
    mpd
end
