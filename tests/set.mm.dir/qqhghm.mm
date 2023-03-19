include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "caddc.mm"
include "cplusg.mm"
include "cqqh.mm"
include "cq.mm"
include "qrngbas.mm"
include "cvv.mm"
include "qex.mm"
include "ccnfld.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "cgrp.mm"
include "qdrng.mm"
include "drnggrp.mm"
include "mp1i.mm"
include "adantr.mm"
include "qqhf.mm"
include "cv.mm"
include "cnumer.mm"
include "cdenom.mm"
include "cmul.mm"
include "co.mm"
include "crg.mm"
include "cui.mm"
include "drngring.mm"
include "ad2antrr.mm"
include "cz.mm"
include "wf.mm"
include "zring.mm"
include "crh.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "3syl.mm"
include "qnumcl.mm"
include "ad2antrl.mm"
include "cn.mm"
include "qdencl.mm"
include "ad2antll.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "ffvelrnd.mm"
include "cmulr.mm"
include "syl.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "wne.mm"
include "simpl.mm"
include "nnne0d.mm"
include "c0g.mm"
include "elzrhunit.mm"
include "syl12anc.mm"
include "unitmulcl.mm"
include "eqeltrd.mm"
include "dvrdir.mm"
include "syl13anc.mm"
include "cdiv.mm"
include "qeqnumdivden.mm"
include "oveq12d.mm"
include "zcnd.mm"
include "divadddivd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "zaddcld.mm"
include "mulne0d.mm"
include "qqhvq.mm"
include "cghm.mm"
include "rhmghm.mm"
include "w3a.mm"
include "zringplusg.mm"
include "ghmlin.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "rhmdvd.mm"
include "syl132anc.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem qqhghm
  let cB: class B
  let c.dv: class ./
  let cQ: class Q
  let cR: class R
  let cL: class L
  let ve: setvar e
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume qqhval2.0: |- B = ( Base ` R )
  assume qqhval2.1: |- ./ = ( /r ` R )
  assume qqhval2.2: |- L = ( ZRHom ` R )
  assume qqhrhm.1: |- Q = ( CCfld |`s QQ )


  assert |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( QQHom ` R ) e. ( Q GrpHom R ) )

  proof
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    wa
    #
    vx
    vy
    caddc
    cR
    cplusg
    cfv
    #
    cQ
    cR
    cR
    cqqh
    cfv
    #
    cq
    cB
    cQ
    qqhrhm.1
    qrngbas
    qqhval2.0
    cq
    cvv
    wcel
    caddc
    cQ
    cplusg
    cfv
    wceq
    qex
    cq
    caddc
    ccnfld
    cQ
    cvv
    qqhrhm.1
    cnfldadd
    ressplusg
    ax-mp
    @3
    eqid
    #
    cQ
    cdr
    wcel
    cQ
    cgrp
    wcel
    @2
    cQ
    qqhrhm.1
    qdrng
    cQ
    drnggrp
    mp1i
    @0
    cR
    cgrp
    wcel
    @1
    cR
    drnggrp
    adantr
    cB
    c.dv
    cR
    cL
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhf
    @2
    vx
    cv
    #
    cq
    wcel
    #
    vy
    cv
    #
    cq
    wcel
    #
    wa
    #
    wa
    #
    @6
    cnumer
    cfv
    #
    @8
    cdenom
    cfv
    #
    cmul
    co
    #
    cL
    cfv
    #
    @8
    cnumer
    cfv
    #
    @6
    cdenom
    cfv
    #
    cmul
    co
    #
    cL
    cfv
    #
    @3
    co
    #
    @17
    @13
    cmul
    co
    #
    cL
    cfv
    #
    c.dv
    co
    #
    @15
    @22
    c.dv
    co
    #
    @19
    @22
    c.dv
    co
    #
    @3
    co
    #
    @6
    @8
    caddc
    co
    #
    @4
    cfv
    #
    @6
    @4
    cfv
    #
    @8
    @4
    cfv
    #
    @3
    co
    @11
    cR
    crg
    wcel
    #
    @15
    cB
    wcel
    @19
    cB
    wcel
    @22
    cR
    cui
    cfv
    #
    wcel
    @23
    @26
    wceq
    @0
    @31
    @1
    @10
    cR
    drngring
    #
    ad2antrr
    #
    @11
    cz
    cB
    @14
    cL
    @2
    cz
    cB
    cL
    wf
    #
    @10
    @2
    @31
    cL
    zring
    cR
    crh
    co
    wcel
    #
    @35
    @0
    @31
    @1
    @33
    adantr
    cR
    cL
    qqhval2.2
    zrhrhm
    #
    cz
    cB
    zring
    cR
    cL
    zringbas
    qqhval2.0
    rhmf
    3syl
    adantr
    #
    @11
    @12
    @13
    @7
    @12
    cz
    wcel
    #
    @2
    @9
    @6
    qnumcl
    ad2antrl
    #
    @11
    @13
    @9
    @13
    cn
    wcel
    @2
    @7
    @8
    qdencl
    ad2antll
    #
    nnzd
    #
    zmulcld
    #
    ffvelrnd
    @11
    cz
    cB
    @18
    cL
    @38
    @11
    @16
    @17
    @9
    @16
    cz
    wcel
    #
    @2
    @7
    @8
    qnumcl
    ad2antll
    #
    @11
    @17
    @7
    @17
    cn
    wcel
    @2
    @9
    @6
    qdencl
    ad2antrl
    #
    nnzd
    #
    zmulcld
    #
    ffvelrnd
    @11
    @22
    @17
    cL
    cfv
    #
    @13
    cL
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @32
    @11
    @36
    @17
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    @22
    @52
    wceq
    @11
    @31
    @36
    @34
    @37
    syl
    #
    @47
    @42
    @17
    @13
    zring
    cR
    cmul
    @51
    cL
    cz
    zringbas
    zringmulr
    @51
    eqid
    #
    rhmmul
    syl3anc
    @11
    @31
    @49
    @32
    wcel
    #
    @50
    @32
    wcel
    #
    @52
    @32
    wcel
    @34
    @11
    @2
    @53
    @17
    cc0
    wne
    #
    @57
    @2
    @10
    simpl
    #
    @47
    @11
    @17
    @46
    nnne0d
    #
    cB
    cR
    cL
    @17
    cR
    c0g
    cfv
    #
    qqhval2.0
    qqhval2.2
    @62
    eqid
    #
    elzrhunit
    syl12anc
    #
    @11
    @2
    @54
    @13
    cc0
    wne
    #
    @58
    @60
    @42
    @11
    @13
    @41
    nnne0d
    #
    cB
    cR
    cL
    @13
    @62
    qqhval2.0
    qqhval2.2
    @63
    elzrhunit
    syl12anc
    #
    cR
    @51
    @32
    @49
    @50
    @32
    eqid
    #
    @56
    unitmulcl
    syl3anc
    eqeltrd
    cB
    c.dv
    @3
    cR
    @32
    @15
    @19
    @22
    qqhval2.0
    @68
    @5
    qqhval2.1
    dvrdir
    syl13anc
    @11
    @28
    @14
    @18
    caddc
    co
    #
    @21
    cdiv
    co
    #
    @4
    cfv
    #
    @69
    cL
    cfv
    #
    @22
    c.dv
    co
    #
    @23
    @11
    @27
    @70
    @4
    @11
    @27
    @12
    @17
    cdiv
    co
    #
    @16
    @13
    cdiv
    co
    #
    caddc
    co
    @70
    @11
    @6
    @74
    @8
    @75
    caddc
    @7
    @6
    @74
    wceq
    @2
    @9
    @6
    qeqnumdivden
    #
    ad2antrl
    @9
    @8
    @75
    wceq
    @2
    @7
    @8
    qeqnumdivden
    #
    ad2antll
    oveq12d
    @11
    @12
    @17
    @16
    @13
    @11
    @12
    @40
    zcnd
    @11
    @17
    @47
    zcnd
    #
    @11
    @16
    @45
    zcnd
    @11
    @13
    @42
    zcnd
    #
    @61
    @66
    divadddivd
    eqtrd
    fveq2d
    @11
    @2
    @69
    cz
    wcel
    @21
    cz
    wcel
    @21
    cc0
    wne
    @71
    @73
    wceq
    @60
    @11
    @14
    @18
    @43
    @48
    zaddcld
    @11
    @17
    @13
    @47
    @42
    zmulcld
    @11
    @17
    @13
    @78
    @79
    @61
    @66
    mulne0d
    cB
    c.dv
    cR
    cL
    @69
    @21
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhvq
    syl13anc
    @11
    cL
    zring
    cR
    cghm
    co
    wcel
    #
    @14
    cz
    wcel
    #
    @18
    cz
    wcel
    #
    @73
    @23
    wceq
    @11
    @36
    @80
    @55
    zring
    cR
    cL
    rhmghm
    syl
    @43
    @48
    @80
    @81
    @82
    w3a
    @72
    @20
    @22
    c.dv
    caddc
    @3
    zring
    cR
    @14
    cL
    @18
    cz
    zringbas
    zringplusg
    @5
    ghmlin
    oveq1d
    syl3anc
    3eqtrd
    @11
    @29
    @24
    @30
    @25
    @3
    @11
    @29
    @74
    @4
    cfv
    #
    @12
    cL
    cfv
    @49
    c.dv
    co
    #
    @24
    @7
    @29
    @83
    wceq
    @2
    @9
    @7
    @6
    @74
    @4
    @76
    fveq2d
    ad2antrl
    @11
    @2
    @39
    @53
    @59
    @83
    @84
    wceq
    @60
    @40
    @47
    @61
    cB
    c.dv
    cR
    cL
    @12
    @17
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhvq
    syl13anc
    @11
    @36
    @39
    @53
    @54
    @57
    @58
    @84
    @24
    wceq
    @55
    @40
    @47
    @42
    @64
    @67
    @12
    @17
    @13
    c.dv
    zring
    cR
    cmul
    @32
    cL
    cz
    @68
    zringbas
    qqhval2.1
    zringmulr
    rhmdvd
    syl132anc
    3eqtrd
    @11
    @30
    @75
    @4
    cfv
    #
    @25
    @9
    @30
    @85
    wceq
    @2
    @7
    @9
    @8
    @75
    @4
    @77
    fveq2d
    ad2antll
    @11
    @16
    cL
    cfv
    @50
    c.dv
    co
    #
    @19
    @13
    @17
    cmul
    co
    #
    cL
    cfv
    #
    c.dv
    co
    #
    @85
    @25
    @11
    @36
    @44
    @54
    @53
    @58
    @57
    @86
    @89
    wceq
    @55
    @45
    @42
    @47
    @67
    @64
    @16
    @13
    @17
    c.dv
    zring
    cR
    cmul
    @32
    cL
    cz
    @68
    zringbas
    qqhval2.1
    zringmulr
    rhmdvd
    syl132anc
    @11
    @2
    @44
    @54
    @65
    @85
    @86
    wceq
    @60
    @45
    @42
    @66
    cB
    c.dv
    cR
    cL
    @16
    @13
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhvq
    syl13anc
    @11
    @22
    @88
    @19
    c.dv
    @11
    @21
    @87
    cL
    @11
    @17
    @13
    @78
    @79
    mulcomd
    fveq2d
    oveq2d
    3eqtr4d
    eqtrd
    oveq12d
    3eqtr4d
    isghmd
end
