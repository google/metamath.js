include "cngp.mm"
include "wcel.mm"
include "cabl.mm"
include "wa.mm"
include "cgrp.mm"
include "ctps.mm"
include "csg.mm"
include "cfv.mm"
include "ctopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "ctgp.mm"
include "ngpgrp.mm"
include "adantr.mm"
include "cmt.mm"
include "ngpms.mm"
include "mstps.mm"
include "syl.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "eqid.mm"
include "grpsubf.mm"
include "c2.mm"
include "cdiv.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "caddc.mm"
include "cr.mm"
include "simplll.mm"
include "simpllr.mm"
include "simpld.mm"
include "simprl.mm"
include "mscl.mm"
include "syl3anc.mm"
include "simprd.mm"
include "simprr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lt2halves.mm"
include "cle.mm"
include "grpsubcl.mm"
include "mstri.mm"
include "syl13anc.mm"
include "wceq.mm"
include "ngpsubcan.mm"
include "cminusg.mm"
include "cplusg.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "grpinvcl.mm"
include "ngplcan.mm"
include "ngpinvds.mm"
include "syl12anc.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "readdcld.mm"
include "lelttr.mm"
include "mpand.mm"
include "syld.mm"
include "ovresd.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "3imtr4d.mm"
include "ralrimivva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "cxmt.mm"
include "wb.mm"
include "cxme.mm"
include "msxms.mm"
include "xmsxmet.mm"
include "3syl.mm"
include "txmetcn.mm"
include "mpbir2and.mm"
include "mstopn.mm"
include "eleqtrrd.mm"
include "istgp2.mm"
include "syl3anbrc.mm"

theorem ngptgp
  let cG: class G
  let vr: setvar r
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( G e. NrmGrp /\ G e. Abel ) -> G e. TopGrp )

  proof
    cG
    cngp
    wcel
    #
    cG
    cabl
    wcel
    #
    wa
    #
    cG
    cgrp
    wcel
    #
    cG
    ctps
    wcel
    #
    cG
    csg
    cfv
    #
    cG
    ctopn
    cfv
    #
    @6
    ctx
    co
    #
    @6
    ccn
    co
    #
    wcel
    cG
    ctgp
    wcel
    @0
    @3
    @1
    cG
    ngpgrp
    adantr
    #
    @2
    cG
    cmt
    wcel
    #
    @4
    @0
    @10
    @1
    cG
    ngpms
    adantr
    #
    cG
    mstps
    syl
    @2
    @5
    cG
    cds
    cfv
    #
    cG
    cbs
    cfv
    #
    @13
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    @16
    ctx
    co
    #
    @16
    ccn
    co
    #
    @8
    @2
    @5
    @18
    wcel
    #
    @14
    @13
    @5
    wf
    #
    vx
    cv
    #
    vu
    cv
    #
    @15
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    vv
    cv
    #
    @15
    co
    #
    @24
    clt
    wbr
    #
    wa
    #
    @21
    @26
    @5
    co
    #
    @22
    @27
    @5
    co
    #
    @15
    co
    #
    vz
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    @13
    wral
    vu
    @13
    wral
    #
    vr
    crp
    wrex
    #
    vz
    crp
    wral
    #
    vy
    @13
    wral
    vx
    @13
    wral
    #
    @2
    @3
    @20
    @9
    @13
    cG
    @5
    @13
    eqid
    #
    @5
    eqid
    #
    grpsubf
    syl
    @2
    @39
    vx
    vy
    @13
    @13
    @2
    @21
    @13
    wcel
    #
    @26
    @13
    wcel
    #
    wa
    #
    wa
    #
    @38
    vz
    crp
    @46
    @34
    crp
    wcel
    #
    wa
    #
    @34
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @23
    @49
    clt
    wbr
    #
    @28
    @49
    clt
    wbr
    #
    wa
    #
    @35
    wi
    #
    vv
    @13
    wral
    vu
    @13
    wral
    #
    @38
    @47
    @50
    @46
    @34
    rphalfcl
    adantl
    @48
    @54
    vu
    vv
    @13
    @13
    @48
    @22
    @13
    wcel
    #
    @27
    @13
    wcel
    #
    wa
    #
    wa
    #
    @21
    @22
    @12
    co
    #
    @49
    clt
    wbr
    #
    @26
    @27
    @12
    co
    #
    @49
    clt
    wbr
    #
    wa
    #
    @31
    @32
    @12
    co
    #
    @34
    clt
    wbr
    #
    @53
    @35
    @59
    @64
    @60
    @62
    caddc
    co
    #
    @34
    clt
    wbr
    #
    @66
    @59
    @60
    cr
    wcel
    #
    @62
    cr
    wcel
    #
    @34
    cr
    wcel
    #
    @64
    @68
    wi
    @59
    @10
    @43
    @56
    @69
    @59
    @2
    @10
    @2
    @45
    @47
    @58
    simplll
    #
    @11
    syl
    #
    @59
    @43
    @44
    @2
    @45
    @47
    @58
    simpllr
    #
    simpld
    #
    @48
    @56
    @57
    simprl
    #
    @21
    @22
    @12
    cG
    @13
    @41
    @12
    eqid
    #
    mscl
    syl3anc
    #
    @59
    @10
    @44
    @57
    @70
    @73
    @59
    @43
    @44
    @74
    simprd
    #
    @48
    @56
    @57
    simprr
    #
    @26
    @27
    @12
    cG
    @13
    @41
    @77
    mscl
    syl3anc
    #
    @47
    @71
    @46
    @58
    @34
    rpre
    ad2antlr
    #
    @60
    @62
    @34
    lt2halves
    syl3anc
    @59
    @65
    @67
    cle
    wbr
    #
    @68
    @66
    @59
    @65
    @31
    @22
    @26
    @5
    co
    #
    @12
    co
    #
    @84
    @32
    @12
    co
    #
    caddc
    co
    #
    @67
    cle
    @59
    @10
    @31
    @13
    wcel
    #
    @32
    @13
    wcel
    #
    @84
    @13
    wcel
    #
    @65
    @87
    cle
    wbr
    @73
    @59
    @3
    @43
    @44
    @88
    @59
    @2
    @3
    @72
    @9
    syl
    #
    @75
    @79
    @13
    cG
    @5
    @21
    @26
    @41
    @42
    grpsubcl
    syl3anc
    #
    @59
    @3
    @56
    @57
    @89
    @91
    @76
    @80
    @13
    cG
    @5
    @22
    @27
    @41
    @42
    grpsubcl
    syl3anc
    #
    @59
    @3
    @56
    @44
    @90
    @91
    @76
    @79
    @13
    cG
    @5
    @22
    @26
    @41
    @42
    grpsubcl
    syl3anc
    @31
    @32
    @84
    @12
    cG
    @13
    @41
    @77
    mstri
    syl13anc
    @59
    @85
    @60
    @86
    @62
    caddc
    @59
    @0
    @43
    @56
    @44
    @85
    @60
    wceq
    @59
    @0
    @1
    @72
    simpld
    @75
    @76
    @79
    @21
    @22
    @26
    @12
    cG
    @5
    @13
    @41
    @42
    @77
    ngpsubcan
    syl13anc
    @59
    @86
    @22
    @26
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @22
    @27
    @94
    cfv
    #
    @96
    co
    #
    @12
    co
    #
    @95
    @98
    @12
    co
    #
    @62
    @59
    @84
    @97
    @32
    @99
    @12
    @59
    @56
    @44
    @84
    @97
    wceq
    @76
    @79
    @13
    @96
    cG
    @94
    @5
    @22
    @26
    @41
    @96
    eqid
    #
    @94
    eqid
    #
    @42
    grpsubval
    syl2anc
    @58
    @32
    @99
    wceq
    @48
    @13
    @96
    cG
    @94
    @5
    @22
    @27
    @41
    @102
    @103
    @42
    grpsubval
    adantl
    oveq12d
    @59
    @2
    @95
    @13
    wcel
    #
    @98
    @13
    wcel
    #
    @56
    @100
    @101
    wceq
    @72
    @59
    @3
    @44
    @104
    @91
    @79
    @13
    cG
    @94
    @26
    @41
    @103
    grpinvcl
    syl2anc
    @59
    @3
    @57
    @105
    @91
    @80
    @13
    cG
    @94
    @27
    @41
    @103
    grpinvcl
    syl2anc
    @76
    @95
    @98
    @22
    @12
    @96
    cG
    @13
    @41
    @102
    @77
    ngplcan
    syl13anc
    @59
    @2
    @44
    @57
    @101
    @62
    wceq
    @72
    @79
    @80
    @26
    @27
    @12
    cG
    @94
    @13
    @41
    @103
    @77
    ngpinvds
    syl12anc
    3eqtrd
    oveq12d
    breqtrd
    @59
    @65
    cr
    wcel
    #
    @67
    cr
    wcel
    @71
    @83
    @68
    wa
    @66
    wi
    @59
    @10
    @88
    @89
    @106
    @73
    @92
    @93
    @31
    @32
    @12
    cG
    @13
    @41
    @77
    mscl
    syl3anc
    @59
    @60
    @62
    @78
    @81
    readdcld
    @82
    @65
    @67
    @34
    lelttr
    syl3anc
    mpand
    syld
    @59
    @51
    @61
    @52
    @63
    @59
    @23
    @60
    @49
    clt
    @59
    @21
    @22
    @12
    @13
    @75
    @76
    ovresd
    breq1d
    @59
    @28
    @62
    @49
    clt
    @59
    @26
    @27
    @12
    @13
    @79
    @80
    ovresd
    breq1d
    anbi12d
    @59
    @33
    @65
    @34
    clt
    @59
    @31
    @32
    @12
    @13
    @92
    @93
    ovresd
    breq1d
    3imtr4d
    ralrimivva
    @37
    @55
    vr
    @49
    crp
    @24
    @49
    wceq
    #
    @36
    @54
    vu
    vv
    @13
    @13
    @107
    @30
    @53
    @35
    @107
    @25
    @51
    @29
    @52
    @24
    @49
    @23
    clt
    breq2
    @24
    @49
    @28
    clt
    breq2
    anbi12d
    imbi1d
    2ralbidv
    rspcev
    syl2anc
    ralrimiva
    ralrimivva
    @2
    @15
    @13
    cxmt
    cfv
    wcel
    #
    @108
    @108
    @19
    @20
    @40
    wa
    wb
    @2
    @10
    cG
    cxme
    wcel
    @108
    @11
    cG
    msxms
    @15
    cG
    @13
    @41
    @15
    eqid
    #
    xmsxmet
    3syl
    #
    @110
    @110
    vx
    vy
    vz
    vr
    vv
    vu
    @15
    @15
    @15
    @5
    @16
    @16
    @16
    @13
    @13
    @13
    @16
    eqid
    #
    @111
    @111
    txmetcn
    syl3anc
    mpbir2and
    @2
    @7
    @17
    @6
    @16
    ccn
    @2
    @6
    @16
    @6
    @16
    ctx
    @2
    @10
    @6
    @16
    wceq
    @11
    @15
    @6
    cG
    @13
    @6
    eqid
    #
    @41
    @109
    mstopn
    syl
    #
    @113
    oveq12d
    @113
    oveq12d
    eleqtrrd
    cG
    @6
    @5
    @112
    @42
    istgp2
    syl3anbrc
end
