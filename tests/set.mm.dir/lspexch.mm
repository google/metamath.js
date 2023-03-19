include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cplusg.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "cpr.mm"
include "wcel.mm"
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
include "cminusg.mm"
include "csg.mm"
include "3ad2ant1.mm"
include "simp2r.mm"
include "csn.mm"
include "cdif.mm"
include "eldifad.mm"
include "lmodsubvs.mm"
include "simp3.mm"
include "eqcomd.mm"
include "cgrp.mm"
include "wb.mm"
include "lmodgrp.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "grpsubadd.mm"
include "syl13anc.mm"
include "mpbird.mm"
include "eqtr3d.mm"
include "c0g.mm"
include "wne.mm"
include "adantr.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "lmod0vlid.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "lspsneli.mm"
include "eqeltrd.mm"
include "eldifsni.mm"
include "lspsneleq.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lmodfgrp.mm"
include "grpinvcl.mm"
include "lmodvacl.mm"
include "lvecinv.mm"
include "clss.mm"
include "lspprcl.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "drnginvrcl.mm"
include "cur.mm"
include "lmodvs1.mm"
include "crg.mm"
include "lmodring.mm"
include "ringidcl.mm"
include "3syl.mm"
include "lsppreli.mm"
include "eqeltrrd.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "3exp.mm"
include "rexlimdvv.mm"

theorem lspexch
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  assume lspexch.v: |- V = ( Base ` W )
  assume lspexch.o: |- .0. = ( 0g ` W )
  assume lspexch.n: |- N = ( LSpan ` W )
  assume lspexch.w: |- ( ph -> W e. LVec )
  assume lspexch.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lspexch.y: |- ( ph -> Y e. V )
  assume lspexch.z: |- ( ph -> Z e. V )
  assume lspexch.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Z } ) )
  assume lspexch.e: |- ( ph -> X e. ( N ` { Y , Z } ) )


  assert |- ( ph -> Y e. ( N ` { X , Z } ) )

  proof
    wph
    cX
    vj
    cv
    #
    cY
    cW
    cvsca
    cfv
    #
    co
    #
    vk
    cv
    #
    cZ
    @1
    co
    #
    cW
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    vj
    @9
    wrex
    #
    cY
    cX
    cZ
    cpr
    cN
    cfv
    #
    wcel
    #
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    wcel
    @10
    lspexch.e
    wph
    @5
    @1
    vj
    @8
    @9
    cN
    cV
    cW
    cY
    cZ
    cX
    vk
    lspexch.v
    @5
    eqid
    #
    @8
    eqid
    #
    @9
    eqid
    #
    @1
    eqid
    #
    lspexch.n
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    lspexch.w
    cW
    lveclmod
    #
    syl
    #
    lspexch.y
    lspexch.z
    lspprel
    mpbid
    wph
    @7
    @12
    vj
    vk
    @9
    @9
    wph
    @0
    @9
    wcel
    #
    @3
    @9
    wcel
    #
    wa
    #
    @7
    @12
    wph
    @23
    @7
    w3a
    #
    cY
    @0
    @8
    cinvr
    cfv
    #
    cfv
    #
    cX
    @3
    @8
    cminusg
    cfv
    #
    cfv
    #
    cZ
    @1
    co
    #
    @5
    co
    #
    @1
    co
    #
    @11
    @24
    @30
    @2
    wceq
    cY
    @31
    wceq
    @24
    cX
    @4
    cW
    csg
    cfv
    #
    co
    #
    @30
    @2
    @24
    @3
    @5
    @1
    @8
    @9
    @32
    @27
    cV
    cW
    cX
    cZ
    lspexch.v
    @13
    @32
    eqid
    #
    @16
    @14
    @15
    @27
    eqid
    #
    @24
    @17
    @18
    wph
    @23
    @17
    @7
    lspexch.w
    3ad2ant1
    #
    @19
    syl
    #
    wph
    @21
    @22
    @7
    simp2r
    #
    @24
    cX
    cV
    c.0
    csn
    #
    wph
    @23
    cX
    cV
    @39
    cdif
    wcel
    #
    @7
    lspexch.x
    3ad2ant1
    #
    eldifad
    #
    wph
    @23
    cZ
    cV
    wcel
    #
    @7
    lspexch.z
    3ad2ant1
    #
    lmodsubvs
    @24
    @33
    @2
    wceq
    #
    @6
    cX
    wceq
    #
    @24
    cX
    @6
    wph
    @23
    @7
    simp3
    #
    eqcomd
    @24
    cW
    cgrp
    wcel
    #
    cX
    cV
    wcel
    #
    @4
    cV
    wcel
    #
    @2
    cV
    wcel
    #
    @45
    @46
    wb
    @24
    @18
    @48
    wph
    @23
    @18
    @7
    @20
    3ad2ant1
    #
    cW
    lmodgrp
    syl
    @42
    @24
    @18
    @22
    @43
    @50
    @37
    @38
    @44
    @3
    @1
    @8
    @9
    cV
    cW
    cZ
    lspexch.v
    @14
    @16
    @15
    lmodvscl
    syl3anc
    #
    @24
    @18
    @21
    cY
    cV
    wcel
    #
    @51
    @37
    wph
    @21
    @22
    @7
    simp2l
    #
    wph
    @23
    @54
    @7
    lspexch.y
    3ad2ant1
    #
    @0
    @1
    @8
    @9
    cV
    cW
    cY
    lspexch.v
    @14
    @16
    @15
    lmodvscl
    syl3anc
    cV
    @5
    cW
    @32
    cX
    @4
    @2
    lspexch.v
    @13
    @34
    grpsubadd
    syl13anc
    mpbird
    eqtr3d
    @24
    @0
    @1
    @8
    @25
    @9
    cV
    cW
    @30
    cY
    @8
    c0g
    cfv
    #
    lspexch.v
    @16
    @14
    @15
    @57
    eqid
    #
    @25
    eqid
    #
    @36
    @24
    @21
    @0
    @57
    wne
    #
    @0
    @9
    @57
    csn
    cdif
    wcel
    @55
    @24
    cX
    csn
    cN
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    wne
    #
    @60
    wph
    @23
    @63
    @7
    lspexch.q
    3ad2ant1
    @24
    @0
    @57
    @61
    @62
    @24
    @0
    @57
    wceq
    #
    @61
    @62
    wceq
    @24
    @64
    wa
    #
    cN
    cV
    cW
    cZ
    cX
    c.0
    lspexch.v
    lspexch.o
    lspexch.n
    @24
    @17
    @64
    @36
    adantr
    @24
    @43
    @64
    @44
    adantr
    @65
    cX
    @4
    @62
    @65
    cX
    @6
    @4
    @24
    @7
    @64
    @47
    adantr
    @64
    @24
    @6
    @57
    cY
    @1
    co
    #
    @4
    @5
    co
    #
    @4
    @64
    @2
    @66
    @4
    @5
    @0
    @57
    cY
    @1
    oveq1
    oveq1d
    @24
    @67
    c.0
    @4
    @5
    co
    #
    @4
    @24
    @66
    c.0
    @4
    @5
    @24
    @18
    @54
    @66
    c.0
    wceq
    @37
    @56
    @1
    @8
    @57
    cV
    cW
    cY
    c.0
    lspexch.v
    @14
    @16
    @58
    lspexch.o
    lmod0vs
    syl2anc
    oveq1d
    @24
    @18
    @50
    @68
    @4
    wceq
    @37
    @53
    @5
    cV
    cW
    @4
    c.0
    lspexch.v
    @13
    lspexch.o
    lmod0vlid
    syl2anc
    eqtrd
    sylan9eqr
    eqtrd
    @24
    @4
    @62
    wcel
    @64
    @24
    @3
    @1
    @8
    @9
    cN
    cV
    cW
    cZ
    lspexch.v
    @16
    @14
    @15
    lspexch.n
    @37
    @38
    @44
    lspsneli
    adantr
    eqeltrd
    @24
    cX
    c.0
    wne
    #
    @64
    @24
    @40
    @69
    @41
    cX
    cV
    c.0
    eldifsni
    syl
    adantr
    lspsneleq
    ex
    necon3d
    mpd
    #
    @0
    @9
    @57
    eldifsn
    sylanbrc
    @24
    @18
    @49
    @29
    cV
    wcel
    #
    @30
    cV
    wcel
    @37
    @42
    @24
    @18
    @28
    @9
    wcel
    #
    @43
    @71
    @37
    @24
    @8
    cgrp
    wcel
    #
    @22
    @72
    @24
    @18
    @73
    @52
    @8
    cW
    @14
    lmodfgrp
    syl
    @38
    @9
    @8
    @27
    @3
    @15
    @35
    grpinvcl
    syl2anc
    #
    @44
    @28
    @1
    @8
    @9
    cV
    cW
    cZ
    lspexch.v
    @14
    @16
    @15
    lmodvscl
    syl3anc
    @5
    cV
    cW
    cX
    @29
    lspexch.v
    @13
    lmodvacl
    syl3anc
    @56
    lvecinv
    mpbid
    @24
    @18
    @11
    cW
    clss
    cfv
    #
    wcel
    @26
    @9
    wcel
    #
    @30
    @11
    wcel
    @31
    @11
    wcel
    @37
    @24
    @75
    cN
    cV
    cW
    cX
    cZ
    lspexch.v
    @75
    eqid
    #
    lspexch.n
    @37
    @42
    @44
    lspprcl
    @24
    @8
    cdr
    wcel
    #
    @21
    @60
    @76
    @24
    @17
    @78
    @36
    @8
    cW
    @14
    lvecdrng
    syl
    @55
    @70
    @9
    @8
    @25
    @0
    @57
    @15
    @58
    @59
    drnginvrcl
    syl3anc
    @24
    @8
    cur
    cfv
    #
    cX
    @1
    co
    #
    @29
    @5
    co
    @30
    @11
    @24
    @80
    cX
    @29
    @5
    @24
    @18
    @49
    @80
    cX
    wceq
    @37
    @42
    @1
    @79
    @8
    cV
    cW
    cX
    lspexch.v
    @14
    @16
    @79
    eqid
    #
    lmodvs1
    syl2anc
    oveq1d
    @24
    @79
    @28
    @5
    @1
    @8
    @9
    cN
    cV
    cW
    cX
    cZ
    lspexch.v
    @13
    @16
    @14
    @15
    lspexch.n
    @37
    @24
    @18
    @8
    crg
    wcel
    @79
    @9
    wcel
    @37
    @8
    cW
    @14
    lmodring
    @9
    @8
    @79
    @15
    @81
    ringidcl
    3syl
    @74
    @42
    @44
    lsppreli
    eqeltrrd
    @9
    @75
    @1
    @11
    @8
    cW
    @26
    @30
    @14
    @16
    @15
    @77
    lssvscl
    syl22anc
    eqeltrd
    3exp
    rexlimdvv
    mpd
end
