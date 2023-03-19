include "clvec.mm"
include "wcel.mm"
include "wss.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "cdif.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "crab.mm"
include "eqid.mm"
include "clmod.mm"
include "lveclmod.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eldifad.mm"
include "lspsolvlem.mm"
include "cinvr.mm"
include "cmulr.mm"
include "cur.mm"
include "cdr.mm"
include "c0g.mm"
include "wne.mm"
include "wceq.mm"
include "lvecdrng.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "wn.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "snssd.mm"
include "unssd.mm"
include "lspssv.mm"
include "ssdifssd.mm"
include "sseldd.mm"
include "lmod0vrid.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "eldifbd.mm"
include "simprr.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "drnginvrl.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "drnginvrcl.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "lmodvs1.mm"
include "3eqtr3d.mm"
include "lspcl.mm"
include "csg.mm"
include "lmodvscl.mm"
include "lmodvpncan.mm"
include "lmodcom.mm"
include "ssun1.mm"
include "a1i.mm"
include "lspss.mm"
include "lspssid.mm"
include "snidg.mm"
include "elun2.mm"
include "3syl.mm"
include "lssvsubcl.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"
include "lssvscl.mm"
include "rexlimddv.mm"

theorem lspsolv
  let cA: class A
  let cS: class S
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let va: setvar a
  let wph: wff ph
  let cF: class F
  let cQ: class Q
  let c.pl: class .+
  let c.x: class .x.
  assume lspsolv.v: |- V = ( Base ` W )
  assume lspsolv.s: |- S = ( LSubSp ` W )
  assume lspsolv.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LVec /\ ( A C_ V /\ Y e. V /\ X e. ( ( N ` ( A u. { Y } ) ) \ ( N ` A ) ) ) ) -> Y e. ( N ` ( A u. { X } ) ) )

  proof
    cW
    clvec
    wcel
    #
    cA
    cV
    wss
    #
    cY
    cV
    wcel
    #
    cX
    cA
    cY
    csn
    #
    cun
    #
    cN
    cfv
    #
    cA
    cN
    cfv
    #
    cdif
    #
    wcel
    #
    w3a
    #
    wa
    #
    cX
    vr
    cv
    #
    cY
    cW
    cvsca
    cfv
    #
    co
    #
    cW
    cplusg
    cfv
    #
    co
    #
    @6
    wcel
    #
    cY
    cA
    cX
    csn
    #
    cun
    #
    cN
    cfv
    #
    wcel
    vr
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    @10
    vz
    cA
    @21
    @14
    vz
    cv
    @13
    @14
    co
    @6
    wcel
    vr
    @21
    wrex
    vz
    cV
    crab
    #
    cS
    @12
    @20
    cN
    cV
    cW
    cX
    cY
    vr
    lspsolv.v
    lspsolv.s
    lspsolv.n
    @20
    eqid
    #
    @21
    eqid
    #
    @14
    eqid
    #
    @12
    eqid
    #
    @22
    eqid
    @0
    cW
    clmod
    wcel
    #
    @9
    cW
    lveclmod
    adantr
    #
    @0
    @1
    @2
    @8
    simpr1
    #
    @0
    @1
    @2
    @8
    simpr2
    #
    @10
    cX
    @5
    @6
    @0
    @1
    @2
    @8
    simpr3
    #
    eldifad
    lspsolvlem
    @10
    @11
    @21
    wcel
    #
    @16
    wa
    #
    wa
    #
    @11
    @20
    cinvr
    cfv
    #
    cfv
    #
    @13
    @12
    co
    #
    cY
    @19
    @34
    @36
    @11
    @20
    cmulr
    cfv
    #
    co
    #
    cY
    @12
    co
    #
    @20
    cur
    cfv
    #
    cY
    @12
    co
    #
    @37
    cY
    @34
    @39
    @41
    cY
    @12
    @34
    @20
    cdr
    wcel
    #
    @32
    @11
    @20
    c0g
    cfv
    #
    wne
    #
    @39
    @41
    wceq
    @0
    @43
    @9
    @33
    @20
    cW
    @23
    lvecdrng
    ad2antrr
    #
    @10
    @32
    @16
    simprl
    #
    @34
    cX
    @44
    cY
    @12
    co
    #
    @14
    co
    #
    @6
    wcel
    #
    wn
    @45
    @34
    @49
    @5
    @6
    @34
    @49
    cX
    @7
    @34
    @49
    cX
    cW
    c0g
    cfv
    #
    @14
    co
    #
    cX
    @34
    @48
    @51
    cX
    @14
    @34
    @27
    @2
    @48
    @51
    wceq
    @10
    @27
    @33
    @28
    adantr
    #
    @10
    @2
    @33
    @30
    adantr
    #
    @12
    @20
    @44
    cV
    cW
    cY
    @51
    lspsolv.v
    @23
    @26
    @44
    eqid
    #
    @51
    eqid
    #
    lmod0vs
    syl2anc
    oveq2d
    @34
    @27
    cX
    cV
    wcel
    #
    @52
    cX
    wceq
    @53
    @34
    @7
    cV
    cX
    @34
    @5
    cV
    @6
    @34
    @27
    @4
    cV
    wss
    @5
    cV
    wss
    @53
    @34
    cA
    @3
    cV
    @10
    @1
    @33
    @29
    adantr
    #
    @34
    cY
    cV
    @54
    snssd
    unssd
    @4
    cN
    cV
    cW
    lspsolv.v
    lspsolv.n
    lspssv
    syl2anc
    ssdifssd
    @10
    @8
    @33
    @31
    adantr
    #
    sseldd
    #
    @14
    cV
    cW
    cX
    @51
    lspsolv.v
    @25
    @56
    lmod0vrid
    syl2anc
    eqtrd
    @59
    eqeltrd
    eldifbd
    @34
    @50
    @11
    @44
    @34
    @16
    @11
    @44
    wceq
    #
    @50
    @10
    @32
    @16
    simprr
    #
    @61
    @15
    @49
    @6
    @61
    @13
    @48
    cX
    @14
    @11
    @44
    cY
    @12
    oveq1
    oveq2d
    eleq1d
    syl5ibcom
    necon3bd
    mpd
    #
    @21
    @20
    @38
    @41
    @35
    @11
    @44
    @24
    @55
    @38
    eqid
    #
    @41
    eqid
    #
    @35
    eqid
    #
    drnginvrl
    syl3anc
    oveq1d
    @34
    @27
    @36
    @21
    wcel
    #
    @32
    @2
    @40
    @37
    wceq
    @53
    @34
    @43
    @32
    @45
    @67
    @46
    @47
    @63
    @21
    @20
    @35
    @11
    @44
    @24
    @55
    @66
    drnginvrcl
    syl3anc
    #
    @47
    @54
    @36
    @11
    @12
    @38
    @20
    @21
    cV
    cW
    cY
    lspsolv.v
    @23
    @26
    @24
    @64
    lmodvsass
    syl13anc
    @34
    @27
    @2
    @42
    cY
    wceq
    @53
    @54
    @12
    @41
    @20
    cV
    cW
    cY
    lspsolv.v
    @23
    @26
    @65
    lmodvs1
    syl2anc
    3eqtr3d
    @34
    @27
    @19
    cS
    wcel
    #
    @67
    @13
    @19
    wcel
    @37
    @19
    wcel
    @53
    @34
    @27
    @18
    cV
    wss
    #
    @69
    @53
    @34
    cA
    @17
    cV
    @58
    @34
    cX
    cV
    @60
    snssd
    unssd
    #
    cS
    @18
    cN
    cV
    cW
    lspsolv.v
    lspsolv.s
    lspsolv.n
    lspcl
    syl2anc
    #
    @68
    @34
    @13
    cX
    @14
    co
    #
    cX
    cW
    csg
    cfv
    #
    co
    #
    @13
    @19
    @34
    @27
    @13
    cV
    wcel
    #
    @57
    @75
    @13
    wceq
    @53
    @34
    @27
    @32
    @2
    @76
    @53
    @47
    @54
    @11
    @12
    @20
    @21
    cV
    cW
    cY
    lspsolv.v
    @23
    @26
    @24
    lmodvscl
    syl3anc
    #
    @60
    @13
    cX
    @14
    @74
    cV
    cW
    lspsolv.v
    @25
    @74
    eqid
    #
    lmodvpncan
    syl3anc
    @34
    @27
    @69
    @73
    @19
    wcel
    cX
    @19
    wcel
    @75
    @19
    wcel
    @53
    @72
    @34
    @73
    @15
    @19
    @34
    @27
    @76
    @57
    @73
    @15
    wceq
    @53
    @77
    @60
    @14
    cV
    cW
    @13
    cX
    lspsolv.v
    @25
    lmodcom
    syl3anc
    @34
    @6
    @19
    @15
    @34
    @27
    @70
    cA
    @18
    wss
    #
    @6
    @19
    wss
    @53
    @71
    @79
    @34
    cA
    @17
    ssun1
    a1i
    cA
    @18
    cN
    cV
    cW
    lspsolv.v
    lspsolv.n
    lspss
    syl3anc
    @62
    sseldd
    eqeltrd
    @34
    @18
    @19
    cX
    @34
    @27
    @70
    @18
    @19
    wss
    @53
    @71
    @18
    cN
    cV
    cW
    lspsolv.v
    lspsolv.n
    lspssid
    syl2anc
    @34
    @57
    cX
    @17
    wcel
    cX
    @18
    wcel
    @60
    cX
    cV
    snidg
    cX
    @17
    cA
    elun2
    3syl
    sseldd
    cS
    @19
    @74
    cW
    @73
    cX
    @78
    lspsolv.s
    lssvsubcl
    syl22anc
    eqeltrrd
    @21
    cS
    @12
    @19
    @20
    cW
    @36
    @13
    @23
    @26
    @24
    lspsolv.s
    lssvscl
    syl22anc
    eqeltrrd
    rexlimddv
end
