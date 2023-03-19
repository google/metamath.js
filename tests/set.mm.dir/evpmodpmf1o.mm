include "cfn.mm"
include "wcel.mm"
include "cevpm.mm"
include "cfv.mm"
include "cdif.mm"
include "wa.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt.mm"
include "cminusg.mm"
include "cpsgn.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "simpll.mm"
include "cgrp.mm"
include "symggrp.mm"
include "ad2antrr.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "evpmss.mm"
include "sseli.mm"
include "adantl.mm"
include "eqid.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "cmul.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cpr.mm"
include "cress.mm"
include "cghm.mm"
include "psgnghm2.mm"
include "cvv.mm"
include "prex.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "ghmlin.mm"
include "psgnodpm.mm"
include "adantr.mm"
include "psgnevpm.mm"
include "adantlr.mm"
include "oveq12d.mm"
include "ax-1cn.mm"
include "mulm1i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "psgnodpmr.mm"
include "fmptd.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "ccnv.mm"
include "symginv.mm"
include "syl.mm"
include "fveq2d.mm"
include "psgninv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "neg1mulneg1e1.mm"
include "3eqtrd.mm"
include "wb.mm"
include "psgnevpmb.mm"
include "mpbir2and.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "eqidd.mm"
include "oveq2.mm"
include "fmptco.mm"
include "c0g.mm"
include "grplinv.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "mpteq2dva.mm"
include "mptresid.mm"
include "grprinv.mm"
include "fcof1od.mm"

theorem evpmodpmf1o
  let cD: class D
  let cP: class P
  let cS: class S
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  assume evpmodpmf1o.s: |- S = ( SymGrp ` D )
  assume evpmodpmf1o.p: |- P = ( Base ` S )

  disjoint S f
  disjoint D f
  disjoint P f
  disjoint F f
  disjoint S g
  disjoint f g
  disjoint D g
  disjoint P g
  disjoint F g
  assert |- ( ( D e. Fin /\ F e. ( P \ ( pmEven ` D ) ) ) -> ( f e. ( pmEven ` D ) |-> ( F ( +g ` S ) f ) ) : ( pmEven ` D ) -1-1-onto-> ( P \ ( pmEven ` D ) ) )

  proof
    cD
    cfn
    wcel
    #
    cF
    cP
    cD
    cevpm
    cfv
    #
    cdif
    #
    wcel
    #
    wa
    #
    @1
    @2
    vf
    @1
    cF
    vf
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    vg
    @2
    cF
    cS
    cminusg
    cfv
    #
    cfv
    #
    vg
    cv
    #
    @6
    co
    #
    cmpt
    #
    @4
    vf
    @1
    @7
    @2
    @8
    @4
    @5
    @1
    wcel
    #
    wa
    #
    @0
    @7
    cP
    wcel
    #
    @7
    cD
    cpsgn
    cfv
    #
    cfv
    #
    c1
    cneg
    #
    wceq
    @7
    @2
    wcel
    @0
    @3
    @14
    simpll
    @15
    cS
    cgrp
    wcel
    #
    cF
    cP
    wcel
    #
    @5
    cP
    wcel
    #
    @16
    @0
    @20
    @3
    @14
    cD
    cS
    cfn
    evpmodpmf1o.s
    symggrp
    #
    ad2antrr
    #
    @3
    @21
    @0
    @14
    cF
    cP
    @1
    eldifi
    #
    ad2antlr
    #
    @14
    @22
    @4
    @1
    cP
    @5
    cD
    cP
    cS
    evpmodpmf1o.s
    evpmodpmf1o.p
    evpmss
    sseli
    adantl
    #
    cP
    @6
    cS
    cF
    @5
    evpmodpmf1o.p
    @6
    eqid
    #
    grpcl
    syl3anc
    @15
    @18
    cF
    @17
    cfv
    #
    @5
    @17
    cfv
    #
    cmul
    co
    #
    @19
    @15
    @17
    cS
    ccnfld
    cmgp
    cfv
    #
    c1
    @19
    cpr
    #
    cress
    co
    #
    cghm
    co
    wcel
    #
    @21
    @22
    @18
    @31
    wceq
    @0
    @35
    @3
    @14
    cD
    cS
    @34
    @17
    evpmodpmf1o.s
    @17
    eqid
    #
    @34
    eqid
    #
    psgnghm2
    #
    ad2antrr
    @26
    @27
    @6
    cmul
    cS
    @34
    cF
    @17
    @5
    cP
    evpmodpmf1o.p
    @28
    @33
    cvv
    wcel
    cmul
    @34
    cplusg
    cfv
    wceq
    c1
    @19
    prex
    @33
    cmul
    @32
    @34
    cvv
    @37
    ccnfld
    cmul
    @32
    @32
    eqid
    cnfldmul
    mgpplusg
    ressplusg
    ax-mp
    #
    ghmlin
    syl3anc
    @15
    @31
    @19
    c1
    cmul
    co
    @19
    @15
    @29
    @19
    @30
    c1
    cmul
    @4
    @29
    @19
    wceq
    #
    @14
    cD
    cP
    cS
    cF
    @17
    evpmodpmf1o.s
    evpmodpmf1o.p
    @36
    psgnodpm
    #
    adantr
    @0
    @14
    @30
    c1
    wceq
    @3
    cD
    cP
    cS
    @5
    @17
    evpmodpmf1o.s
    evpmodpmf1o.p
    @36
    psgnevpm
    adantlr
    oveq12d
    c1
    ax-1cn
    mulm1i
    syl6eq
    eqtrd
    cD
    cP
    cS
    @7
    @17
    evpmodpmf1o.s
    evpmodpmf1o.p
    @36
    psgnodpmr
    syl3anc
    #
    @8
    eqid
    fmptd
    @4
    vg
    @2
    @12
    @1
    @13
    @4
    @11
    @2
    wcel
    #
    wa
    #
    @12
    @1
    wcel
    #
    @12
    cP
    wcel
    #
    @12
    @17
    cfv
    #
    c1
    wceq
    #
    @44
    @20
    @10
    cP
    wcel
    #
    @11
    cP
    wcel
    #
    @46
    @0
    @20
    @3
    @43
    @23
    ad2antrr
    #
    @4
    @49
    @43
    @0
    @20
    @21
    @49
    @3
    @23
    @25
    cP
    cS
    @9
    cF
    evpmodpmf1o.p
    @9
    eqid
    #
    grpinvcl
    syl2an
    #
    adantr
    #
    @43
    @50
    @4
    @11
    cP
    @1
    eldifi
    adantl
    #
    cP
    @6
    cS
    @10
    @11
    evpmodpmf1o.p
    @28
    grpcl
    syl3anc
    @44
    @47
    @10
    @17
    cfv
    #
    @11
    @17
    cfv
    #
    cmul
    co
    #
    cF
    ccnv
    #
    @17
    cfv
    #
    @19
    cmul
    co
    #
    c1
    @44
    @35
    @49
    @50
    @47
    @58
    wceq
    @0
    @35
    @3
    @43
    @38
    ad2antrr
    @54
    @55
    @6
    cmul
    cS
    @34
    @10
    @17
    @11
    cP
    evpmodpmf1o.p
    @28
    @39
    ghmlin
    syl3anc
    @44
    @56
    @60
    @57
    @19
    cmul
    @44
    @10
    @59
    @17
    @3
    @10
    @59
    wceq
    #
    @0
    @43
    @3
    @21
    @62
    @25
    cD
    cP
    cF
    cS
    @9
    evpmodpmf1o.s
    evpmodpmf1o.p
    @52
    symginv
    syl
    ad2antlr
    fveq2d
    @0
    @43
    @57
    @19
    wceq
    @3
    cD
    cP
    cS
    @11
    @17
    evpmodpmf1o.s
    evpmodpmf1o.p
    @36
    psgnodpm
    adantlr
    oveq12d
    @44
    @61
    @19
    @19
    cmul
    co
    c1
    @44
    @60
    @19
    @19
    cmul
    @44
    @60
    @29
    @19
    @44
    @0
    @21
    @60
    @29
    wceq
    @0
    @3
    @43
    simpll
    @3
    @21
    @0
    @43
    @25
    ad2antlr
    #
    cD
    cP
    cS
    cF
    @17
    evpmodpmf1o.s
    @36
    evpmodpmf1o.p
    psgninv
    syl2anc
    @4
    @40
    @43
    @41
    adantr
    eqtrd
    oveq1d
    neg1mulneg1e1
    syl6eq
    3eqtrd
    @0
    @45
    @46
    @48
    wa
    wb
    @3
    @43
    cD
    cP
    cS
    @12
    @17
    evpmodpmf1o.s
    evpmodpmf1o.p
    @36
    psgnevpmb
    ad2antrr
    mpbir2and
    #
    @13
    eqid
    fmptd
    @4
    @13
    @8
    ccom
    #
    vf
    @1
    @5
    cmpt
    #
    cid
    @1
    cres
    @4
    @65
    vf
    @1
    @10
    @7
    @6
    co
    #
    cmpt
    @66
    @4
    vf
    vg
    @1
    @2
    @7
    @12
    @67
    @8
    @13
    @42
    @4
    @8
    eqidd
    #
    @4
    @13
    eqidd
    #
    @11
    @7
    @10
    @6
    oveq2
    fmptco
    @4
    vf
    @1
    @67
    @5
    @15
    @10
    cF
    @6
    co
    #
    @5
    @6
    co
    #
    cS
    c0g
    cfv
    #
    @5
    @6
    co
    #
    @67
    @5
    @15
    @70
    @72
    @5
    @6
    @15
    @20
    @21
    @70
    @72
    wceq
    @24
    @26
    cP
    @6
    cS
    @9
    cF
    @72
    evpmodpmf1o.p
    @28
    @72
    eqid
    #
    @52
    grplinv
    syl2anc
    oveq1d
    @15
    @20
    @49
    @21
    @22
    @71
    @67
    wceq
    @24
    @4
    @49
    @14
    @53
    adantr
    @26
    @27
    cP
    @6
    cS
    @10
    cF
    @5
    evpmodpmf1o.p
    @28
    grpass
    syl13anc
    @15
    @20
    @22
    @73
    @5
    wceq
    @24
    @27
    cP
    @6
    cS
    @5
    @72
    evpmodpmf1o.p
    @28
    @74
    grplid
    syl2anc
    3eqtr3d
    mpteq2dva
    eqtrd
    vf
    @1
    mptresid
    syl6eq
    @4
    @8
    @13
    ccom
    #
    vg
    @2
    @11
    cmpt
    #
    cid
    @2
    cres
    @4
    @75
    vg
    @2
    cF
    @12
    @6
    co
    #
    cmpt
    @76
    @4
    vg
    vf
    @2
    @1
    @12
    @7
    @77
    @13
    @8
    @64
    @69
    @68
    @5
    @12
    cF
    @6
    oveq2
    fmptco
    @4
    vg
    @2
    @77
    @11
    @44
    cF
    @10
    @6
    co
    #
    @11
    @6
    co
    #
    @72
    @11
    @6
    co
    #
    @77
    @11
    @4
    @79
    @80
    wceq
    @43
    @4
    @78
    @72
    @11
    @6
    @0
    @20
    @21
    @78
    @72
    wceq
    @3
    @23
    @25
    cP
    @6
    cS
    @9
    cF
    @72
    evpmodpmf1o.p
    @28
    @74
    @52
    grprinv
    syl2an
    oveq1d
    adantr
    @44
    @20
    @21
    @49
    @50
    @79
    @77
    wceq
    @51
    @63
    @54
    @55
    cP
    @6
    cS
    cF
    @10
    @11
    evpmodpmf1o.p
    @28
    grpass
    syl13anc
    @44
    @20
    @50
    @80
    @11
    wceq
    @51
    @55
    cP
    @6
    cS
    @11
    @72
    evpmodpmf1o.p
    @28
    @74
    grplid
    syl2anc
    3eqtr3d
    mpteq2dva
    eqtrd
    vg
    @2
    mptresid
    syl6eq
    fcof1od
end
