include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "csn.mm"
include "wcel.mm"
include "cdif.mm"
include "cpr.mm"
include "eqid.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspprel.mm"
include "mpbid.mm"
include "wa.mm"
include "w3a.mm"
include "cinvr.mm"
include "wne.mm"
include "clss.mm"
include "3ad2ant1.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "cdr.mm"
include "c0g.mm"
include "lvecdrng.mm"
include "simp2l.mm"
include "wn.mm"
include "simpl3.mm"
include "simpr.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "lmod0vs.mm"
include "eqtrd.mm"
include "simp2r.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "adantr.mm"
include "lmod0vlid.mm"
include "3eqtrd.mm"
include "simpl2r.mm"
include "lspsnid.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"
include "drnginvrcl.mm"
include "drnginvrn0.mm"
include "oveq1.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "lmod0vrid.mm"
include "preq2.mm"
include "fveq2d.mm"
include "lsppr0.mm"
include "eleqtrd.mm"
include "lvecvsn0.mm"
include "mpbir2and.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simp3.mm"
include "lmodvacl.mm"
include "lspsnvs.mm"
include "syl121anc.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "cmulr.mm"
include "cur.mm"
include "drnginvrl.mm"
include "lmodvsass.mm"
include "lmodvs1.mm"
include "3eqtr3d.mm"
include "sneqd.mm"
include "eqtr3d.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "3exp.mm"
include "rexlimdvv.mm"

theorem lspfixed
  let wph: wff ph
  let vz: setvar z
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vl: setvar l
  assume lspfixed.v: |- V = ( Base ` W )
  assume lspfixed.p: |- .+ = ( +g ` W )
  assume lspfixed.o: |- .0. = ( 0g ` W )
  assume lspfixed.n: |- N = ( LSpan ` W )
  assume lspfixed.w: |- ( ph -> W e. LVec )
  assume lspfixed.x: |- ( ph -> X e. V )
  assume lspfixed.y: |- ( ph -> Y e. V )
  assume lspfixed.z: |- ( ph -> Z e. V )
  assume lspfixed.e: |- ( ph -> -. X e. ( N ` { Y } ) )
  assume lspfixed.f: |- ( ph -> -. X e. ( N ` { Z } ) )
  assume lspfixed.g: |- ( ph -> X e. ( N ` { Y , Z } ) )

  disjoint N z
  disjoint .0. z
  disjoint .+ z
  disjoint W z
  disjoint X z
  disjoint Y z
  disjoint Z z
  disjoint k l
  disjoint k z
  disjoint N k
  disjoint l z
  disjoint N l
  disjoint .0. k
  disjoint .0. l
  disjoint .+ k
  disjoint .+ l
  disjoint V k
  disjoint V l
  disjoint W k
  disjoint W l
  disjoint X k
  disjoint X l
  disjoint Y k
  disjoint Y l
  disjoint Z k
  disjoint Z l
  disjoint k ph
  disjoint l ph
  assert |- ( ph -> E. z e. ( ( N ` { Z } ) \ { .0. } ) X e. ( N ` { ( Y .+ z ) } ) )

  proof
    wph
    cX
    vk
    cv
    #
    cY
    cW
    cvsca
    cfv
    #
    co
    #
    vl
    cv
    #
    cZ
    @1
    co
    #
    c.pl
    co
    #
    wceq
    #
    vl
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    vk
    @8
    wrex
    #
    cX
    cY
    vz
    cv
    #
    c.pl
    co
    #
    csn
    #
    cN
    cfv
    #
    wcel
    #
    vz
    cZ
    csn
    cN
    cfv
    #
    c.0
    csn
    cdif
    #
    wrex
    #
    wph
    cX
    cY
    cZ
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    @9
    lspfixed.g
    wph
    c.pl
    @1
    vk
    @7
    @8
    cN
    cV
    cW
    cY
    cZ
    cX
    vl
    lspfixed.v
    lspfixed.p
    @7
    eqid
    #
    @8
    eqid
    #
    @1
    eqid
    #
    lspfixed.n
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    lspfixed.w
    cW
    lveclmod
    syl
    #
    lspfixed.y
    lspfixed.z
    lspprel
    mpbid
    wph
    @6
    @17
    vk
    vl
    @8
    @8
    wph
    @0
    @8
    wcel
    #
    @3
    @8
    wcel
    #
    wa
    #
    @6
    @17
    wph
    @29
    @6
    w3a
    #
    @0
    @7
    cinvr
    cfv
    #
    cfv
    #
    @4
    @1
    co
    #
    @16
    wcel
    #
    cX
    cY
    @33
    c.pl
    co
    #
    csn
    #
    cN
    cfv
    #
    wcel
    #
    @17
    @30
    @33
    @15
    wcel
    #
    @33
    c.0
    wne
    #
    @34
    @30
    @25
    @15
    cW
    clss
    cfv
    #
    wcel
    #
    @32
    @8
    wcel
    #
    @4
    @15
    wcel
    #
    @39
    wph
    @29
    @25
    @6
    @26
    3ad2ant1
    #
    wph
    @29
    @42
    @6
    wph
    @25
    cZ
    cV
    wcel
    #
    @42
    @26
    lspfixed.z
    @41
    cN
    cV
    cW
    cZ
    lspfixed.v
    @41
    eqid
    #
    lspfixed.n
    lspsncl
    syl2anc
    #
    3ad2ant1
    #
    @30
    @7
    cdr
    wcel
    #
    @27
    @0
    @7
    c0g
    cfv
    #
    wne
    #
    @43
    @30
    @24
    @50
    wph
    @29
    @24
    @6
    lspfixed.w
    3ad2ant1
    #
    @7
    cW
    @21
    lvecdrng
    syl
    #
    wph
    @27
    @28
    @6
    simp2l
    #
    @30
    cX
    @15
    wcel
    #
    wn
    #
    @52
    wph
    @29
    @57
    @6
    lspfixed.f
    3ad2ant1
    @30
    @56
    @0
    @51
    @30
    @0
    @51
    wceq
    #
    @56
    @30
    @58
    wa
    #
    cX
    @4
    @15
    @59
    cX
    @5
    c.0
    @4
    c.pl
    co
    #
    @4
    wph
    @29
    @6
    @58
    simpl3
    @59
    @2
    c.0
    @4
    c.pl
    @59
    @2
    @51
    cY
    @1
    co
    #
    c.0
    @59
    @0
    @51
    cY
    @1
    @30
    @58
    simpr
    oveq1d
    @59
    @25
    cY
    cV
    wcel
    #
    @61
    c.0
    wceq
    @59
    wph
    @25
    wph
    @29
    @6
    @58
    simpl1
    #
    @26
    syl
    #
    @59
    wph
    @62
    @63
    lspfixed.y
    syl
    @1
    @7
    @51
    cV
    cW
    cY
    c.0
    lspfixed.v
    @21
    @23
    @51
    eqid
    #
    lspfixed.o
    lmod0vs
    syl2anc
    eqtrd
    oveq1d
    @59
    @25
    @4
    cV
    wcel
    #
    @60
    @4
    wceq
    @64
    @30
    @66
    @58
    @30
    @25
    @28
    @46
    @66
    @45
    wph
    @27
    @28
    @6
    simp2r
    #
    wph
    @29
    @46
    @6
    lspfixed.z
    3ad2ant1
    #
    @3
    @1
    @7
    @8
    cV
    cW
    cZ
    lspfixed.v
    @21
    @23
    @22
    lmodvscl
    syl3anc
    #
    adantr
    c.pl
    cV
    cW
    @4
    c.0
    lspfixed.v
    lspfixed.p
    lspfixed.o
    lmod0vlid
    syl2anc
    3eqtrd
    @59
    @25
    @42
    @28
    cZ
    @15
    wcel
    #
    @44
    @64
    @59
    wph
    @42
    @63
    @48
    syl
    @27
    @28
    wph
    @6
    @58
    simpl2r
    @59
    wph
    @70
    @63
    wph
    @25
    @46
    @70
    @26
    lspfixed.z
    cN
    cV
    cW
    cZ
    lspfixed.v
    lspfixed.n
    lspsnid
    syl2anc
    #
    syl
    @8
    @41
    @1
    @15
    @7
    cW
    @3
    cZ
    @21
    @23
    @22
    @47
    lssvscl
    #
    syl22anc
    eqeltrd
    ex
    necon3bd
    mpd
    #
    @8
    @7
    @31
    @0
    @51
    @22
    @65
    @31
    eqid
    #
    drnginvrcl
    syl3anc
    #
    @30
    @25
    @42
    @28
    @70
    @44
    @45
    @49
    @67
    wph
    @29
    @70
    @6
    @71
    3ad2ant1
    @72
    syl22anc
    @8
    @41
    @1
    @15
    @7
    cW
    @32
    @4
    @21
    @23
    @22
    @47
    lssvscl
    syl22anc
    @30
    @40
    @32
    @51
    wne
    #
    @4
    c.0
    wne
    #
    @30
    @50
    @27
    @52
    @76
    @54
    @55
    @73
    @8
    @7
    @31
    @0
    @51
    @22
    @65
    @74
    drnginvrn0
    syl3anc
    #
    @30
    @77
    @3
    @51
    wne
    #
    cZ
    c.0
    wne
    #
    @30
    cX
    cY
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @79
    wph
    @29
    @83
    @6
    lspfixed.e
    3ad2ant1
    #
    @30
    @82
    @3
    @51
    @30
    @3
    @51
    wceq
    #
    @82
    @30
    @85
    wa
    #
    cX
    @2
    @81
    @86
    cX
    @5
    @2
    c.0
    c.pl
    co
    #
    @2
    wph
    @29
    @6
    @85
    simpl3
    @86
    @4
    c.0
    @2
    c.pl
    @85
    @30
    @4
    @51
    cZ
    @1
    co
    #
    c.0
    @3
    @51
    cZ
    @1
    oveq1
    @30
    @25
    @46
    @88
    c.0
    wceq
    @45
    @68
    @1
    @7
    @51
    cV
    cW
    cZ
    c.0
    lspfixed.v
    @21
    @23
    @65
    lspfixed.o
    lmod0vs
    syl2anc
    sylan9eqr
    oveq2d
    @30
    @87
    @2
    wceq
    #
    @85
    @30
    @25
    @2
    cV
    wcel
    #
    @89
    @45
    @30
    @25
    @27
    @62
    @90
    @45
    @55
    wph
    @29
    @62
    @6
    lspfixed.y
    3ad2ant1
    #
    @0
    @1
    @7
    @8
    cV
    cW
    cY
    lspfixed.v
    @21
    @23
    @22
    lmodvscl
    syl3anc
    #
    c.pl
    cV
    cW
    @2
    c.0
    lspfixed.v
    lspfixed.p
    lspfixed.o
    lmod0vrid
    syl2anc
    adantr
    3eqtrd
    @30
    @2
    @81
    wcel
    #
    @85
    @30
    @25
    @81
    @41
    wcel
    #
    @27
    cY
    @81
    wcel
    #
    @93
    @45
    wph
    @29
    @94
    @6
    wph
    @25
    @62
    @94
    @26
    lspfixed.y
    @41
    cN
    cV
    cW
    cY
    lspfixed.v
    @47
    lspfixed.n
    lspsncl
    syl2anc
    3ad2ant1
    @55
    wph
    @29
    @95
    @6
    wph
    @25
    @62
    @95
    @26
    lspfixed.y
    cN
    cV
    cW
    cY
    lspfixed.v
    lspfixed.n
    lspsnid
    syl2anc
    3ad2ant1
    @8
    @41
    @1
    @81
    @7
    cW
    @0
    cY
    @21
    @23
    @22
    @47
    lssvscl
    syl22anc
    adantr
    eqeltrd
    ex
    necon3bd
    mpd
    @30
    @83
    @80
    @84
    @30
    @82
    cZ
    c.0
    @30
    cZ
    c.0
    wceq
    #
    @82
    @30
    @96
    wa
    #
    cX
    @19
    @81
    @97
    wph
    @20
    wph
    @29
    @6
    @96
    simpl1
    lspfixed.g
    syl
    @96
    @30
    @19
    cY
    c.0
    cpr
    #
    cN
    cfv
    @81
    @96
    @18
    @98
    cN
    cZ
    c.0
    cY
    preq2
    fveq2d
    @30
    cN
    cV
    cW
    cY
    c.0
    lspfixed.v
    lspfixed.o
    lspfixed.n
    @45
    @91
    lsppr0
    sylan9eqr
    eleqtrd
    ex
    necon3bd
    mpd
    @30
    @3
    @1
    @7
    @8
    @51
    cV
    cW
    cZ
    c.0
    lspfixed.v
    @23
    @21
    @22
    @65
    lspfixed.o
    @53
    @67
    @68
    lvecvsn0
    mpbir2and
    @30
    @32
    @1
    @7
    @8
    @51
    cV
    cW
    @4
    c.0
    lspfixed.v
    @23
    @21
    @22
    @65
    lspfixed.o
    @53
    @75
    @69
    lvecvsn0
    mpbir2and
    @33
    @15
    c.0
    eldifsn
    sylanbrc
    @30
    cX
    @5
    csn
    cN
    cfv
    #
    @37
    @30
    cX
    @5
    @99
    wph
    @29
    @6
    simp3
    @30
    @25
    @5
    cV
    wcel
    #
    @5
    @99
    wcel
    @45
    @30
    @25
    @90
    @66
    @100
    @45
    @92
    @69
    c.pl
    cV
    cW
    @2
    @4
    lspfixed.v
    lspfixed.p
    lmodvacl
    syl3anc
    #
    cN
    cV
    cW
    @5
    lspfixed.v
    lspfixed.n
    lspsnid
    syl2anc
    eqeltrd
    @30
    @32
    @5
    @1
    co
    #
    csn
    #
    cN
    cfv
    #
    @99
    @37
    @30
    @24
    @43
    @76
    @100
    @104
    @99
    wceq
    @53
    @75
    @78
    @101
    @32
    @1
    @7
    @8
    cN
    cV
    cW
    @5
    @51
    lspfixed.v
    @21
    @23
    @22
    @65
    lspfixed.n
    lspsnvs
    syl121anc
    @30
    @103
    @36
    cN
    @30
    @102
    @35
    @30
    @102
    @32
    @2
    @1
    co
    #
    @33
    c.pl
    co
    #
    @35
    @30
    @25
    @43
    @90
    @66
    @102
    @106
    wceq
    @45
    @75
    @92
    @69
    c.pl
    @32
    @1
    @7
    @8
    cV
    cW
    @2
    @4
    lspfixed.v
    lspfixed.p
    @21
    @23
    @22
    lmodvsdi
    syl13anc
    @30
    @105
    cY
    @33
    c.pl
    @30
    @32
    @0
    @7
    cmulr
    cfv
    #
    co
    #
    cY
    @1
    co
    #
    @7
    cur
    cfv
    #
    cY
    @1
    co
    #
    @105
    cY
    @30
    @108
    @110
    cY
    @1
    @30
    @50
    @27
    @52
    @108
    @110
    wceq
    @54
    @55
    @73
    @8
    @7
    @107
    @110
    @31
    @0
    @51
    @22
    @65
    @107
    eqid
    #
    @110
    eqid
    #
    @74
    drnginvrl
    syl3anc
    oveq1d
    @30
    @25
    @43
    @27
    @62
    @109
    @105
    wceq
    @45
    @75
    @55
    @91
    @32
    @0
    @1
    @107
    @7
    @8
    cV
    cW
    cY
    lspfixed.v
    @21
    @23
    @22
    @112
    lmodvsass
    syl13anc
    @30
    @25
    @62
    @111
    cY
    wceq
    @45
    @91
    @1
    @110
    @7
    cV
    cW
    cY
    lspfixed.v
    @21
    @23
    @113
    lmodvs1
    syl2anc
    3eqtr3d
    oveq1d
    eqtrd
    sneqd
    fveq2d
    eqtr3d
    eleqtrd
    @14
    @38
    vz
    @33
    @16
    @10
    @33
    wceq
    #
    @13
    @37
    cX
    @114
    @12
    @36
    cN
    @114
    @11
    @35
    @10
    @33
    cY
    c.pl
    oveq2
    sneqd
    fveq2d
    eleq2d
    rspcev
    syl2anc
    3exp
    rexlimdvv
    mpd
end
