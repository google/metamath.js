include "cidom.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cv1.mm"
include "cfv.mm"
include "cpl1.mm"
include "cmgp.mm"
include "cmg.mm"
include "co.mm"
include "cascl.mm"
include "csg.mm"
include "ce1.mm"
include "ccnv.mm"
include "c0g.mm"
include "csn.mm"
include "cima.mm"
include "chash.mm"
include "cdg1.mm"
include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "cle.mm"
include "cbs.mm"
include "eqid.mm"
include "simp1.mm"
include "cgrp.mm"
include "crg.mm"
include "ccrg.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "syl.mm"
include "crngring.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "cmgm.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mndmgm.mm"
include "simp3.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnncl.mm"
include "syl3anc.mm"
include "wf.mm"
include "ply1sclf.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "grpsubcl.mm"
include "wne.mm"
include "cn0.mm"
include "clt.mm"
include "cc0.mm"
include "cxr.mm"
include "deg1xrcl.mm"
include "0xr.mm"
include "a1i.mm"
include "nnre.mm"
include "rexrd.mm"
include "3ad2ant3.mm"
include "wbr.mm"
include "deg1sclle.mm"
include "syl2anc.mm"
include "nngt0.mm"
include "xrlelttrd.mm"
include "cnzr.mm"
include "simprbi.mm"
include "domnnzr.mm"
include "nnnn0.mm"
include "deg1pw.mm"
include "breqtrrd.mm"
include "deg1sub.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "wb.mm"
include "deg1nn0clb.mm"
include "mpbird.mm"
include "fta1g.mm"
include "wfn.mm"
include "cpws.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "crh.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fniniseg2.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "evl1vard.mm"
include "simpl3.mm"
include "evl1expd.mm"
include "simpl2.mm"
include "evl1scad.mm"
include "evl1subd.mm"
include "simprd.mm"
include "eqeq1d.mm"
include "grpsubeq0.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "fveq2d.mm"
include "3brtr3d.mm"

theorem idomrootle
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.ex: class .^
  let cN: class N
  let cX: class X
  assume idomrootle.b: |- B = ( Base ` R )
  assume idomrootle.e: |- .^ = ( .g ` ( mulGrp ` R ) )

  disjoint B y
  disjoint N y
  disjoint R y
  disjoint X y
  assert |- ( ( R e. IDomn /\ X e. B /\ N e. NN ) -> ( # ` { y e. B | ( N .^ y ) = X } ) <_ N )

  proof
    cR
    cidom
    wcel
    #
    cX
    cB
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cN
    cR
    cv1
    cfv
    #
    cR
    cpl1
    cfv
    #
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cX
    @5
    cascl
    cfv
    #
    cfv
    #
    @5
    csg
    cfv
    #
    co
    #
    cR
    ce1
    cfv
    #
    cfv
    #
    ccnv
    cR
    c0g
    cfv
    #
    csn
    cima
    #
    chash
    cfv
    @12
    cR
    cdg1
    cfv
    #
    cfv
    #
    cN
    vy
    cv
    #
    c.ex
    co
    #
    cX
    wceq
    #
    vy
    cB
    crab
    #
    chash
    cfv
    cN
    cle
    @3
    @5
    cbs
    cfv
    #
    @17
    @5
    cR
    @12
    @13
    @15
    @5
    c0g
    cfv
    #
    @5
    eqid
    #
    @23
    eqid
    #
    @17
    eqid
    #
    @13
    eqid
    #
    @15
    eqid
    #
    @24
    eqid
    #
    @0
    @1
    @2
    simp1
    #
    @3
    @5
    cgrp
    wcel
    #
    @8
    @23
    wcel
    #
    @10
    @23
    wcel
    #
    @12
    @23
    wcel
    #
    @3
    @5
    crg
    wcel
    #
    @32
    @3
    cR
    crg
    wcel
    #
    @36
    @3
    cR
    ccrg
    wcel
    #
    @37
    @3
    @0
    @38
    @31
    @0
    @38
    cR
    cdomn
    wcel
    #
    cR
    isidom
    #
    simplbi
    syl
    #
    cR
    crngring
    syl
    #
    @5
    cR
    @25
    ply1ring
    syl
    #
    @5
    ringgrp
    syl
    @3
    @6
    cmgm
    wcel
    #
    @2
    @4
    @23
    wcel
    #
    @33
    @3
    @6
    cmnd
    wcel
    #
    @44
    @3
    @36
    @46
    @43
    @5
    @6
    @6
    eqid
    #
    ringmgp
    syl
    @6
    mndmgm
    syl
    @0
    @1
    @2
    simp3
    @3
    @37
    @45
    @42
    @23
    @5
    cR
    @4
    @4
    eqid
    #
    @25
    @26
    vr1cl
    syl
    @23
    @7
    @6
    cN
    @4
    @23
    @5
    @6
    @47
    @26
    mgpbas
    @7
    eqid
    #
    mulgnncl
    syl3anc
    #
    @3
    cB
    @23
    cX
    @9
    @3
    @37
    cB
    @23
    @9
    wf
    @42
    @9
    @23
    @5
    cR
    cB
    @25
    @9
    eqid
    #
    idomrootle.b
    @26
    ply1sclf
    syl
    @0
    @1
    @2
    simp2
    #
    ffvelrnd
    #
    @23
    @5
    @11
    @8
    @10
    @26
    @11
    eqid
    #
    grpsubcl
    syl3anc
    #
    @3
    @12
    @24
    wne
    #
    @18
    cn0
    wcel
    #
    @3
    @18
    cN
    cn0
    @3
    @18
    @8
    @17
    cfv
    #
    cN
    @3
    @23
    @17
    cR
    @8
    @10
    @11
    @5
    @25
    @27
    @42
    @26
    @54
    @50
    @53
    @3
    @10
    @17
    cfv
    #
    cN
    @58
    clt
    @3
    @59
    cc0
    cN
    @3
    @34
    @59
    cxr
    wcel
    @53
    @23
    @17
    @5
    cR
    @10
    @27
    @25
    @26
    deg1xrcl
    syl
    cc0
    cxr
    wcel
    @3
    0xr
    a1i
    @2
    @0
    cN
    cxr
    wcel
    @1
    @2
    cN
    cN
    nnre
    rexrd
    3ad2ant3
    @3
    @37
    @1
    @59
    cc0
    cle
    wbr
    @42
    @52
    @9
    @17
    @5
    cR
    cX
    cB
    @27
    @25
    idomrootle.b
    @51
    deg1sclle
    syl2anc
    @2
    @0
    cc0
    cN
    clt
    wbr
    @1
    cN
    nngt0
    3ad2ant3
    xrlelttrd
    @3
    cR
    cnzr
    wcel
    #
    cN
    cn0
    wcel
    #
    @58
    cN
    wceq
    @3
    @0
    @60
    @31
    @0
    @39
    @60
    @0
    @38
    @39
    @40
    simprbi
    cR
    domnnzr
    syl
    syl
    @2
    @0
    @61
    @1
    cN
    nnnn0
    #
    3ad2ant3
    #
    @17
    @5
    cR
    @7
    cN
    @6
    @4
    @27
    @25
    @48
    @47
    @49
    deg1pw
    syl2anc
    #
    breqtrrd
    deg1sub
    @64
    eqtrd
    #
    @63
    eqeltrd
    @3
    @37
    @35
    @56
    @57
    wb
    @42
    @55
    @23
    @17
    @5
    cR
    @12
    @24
    @27
    @25
    @30
    @26
    deg1nn0clb
    syl2anc
    mpbird
    fta1g
    @3
    @16
    @22
    chash
    @3
    @16
    @19
    @14
    cfv
    #
    @15
    wceq
    #
    vy
    cB
    crab
    #
    @22
    @3
    @14
    cB
    wfn
    #
    @16
    @68
    wceq
    @3
    cB
    cB
    @14
    wf
    @69
    @3
    cB
    cR
    cB
    cR
    cB
    cpws
    co
    #
    cbs
    cfv
    #
    cidom
    @14
    @70
    cvv
    @70
    eqid
    #
    idomrootle.b
    @71
    eqid
    #
    @31
    cB
    cvv
    wcel
    @3
    cB
    cR
    cbs
    cfv
    cvv
    idomrootle.b
    cR
    cbs
    fvex
    eqeltri
    a1i
    @3
    @23
    @71
    @12
    @13
    @3
    @13
    @5
    @70
    crh
    co
    wcel
    #
    @23
    @71
    @13
    wf
    @3
    @38
    @74
    @41
    cB
    @5
    cR
    @70
    @13
    @28
    @25
    @72
    idomrootle.b
    evl1rhm
    syl
    @23
    @71
    @5
    @70
    @13
    @26
    @73
    rhmf
    syl
    @55
    ffvelrnd
    pwselbas
    cB
    cB
    @14
    ffn
    syl
    vy
    cB
    @15
    @14
    fniniseg2
    syl
    @3
    @67
    @21
    vy
    cB
    @3
    @19
    cB
    wcel
    #
    wa
    #
    @67
    @20
    cX
    cR
    csg
    cfv
    #
    co
    #
    @15
    wceq
    #
    @21
    @76
    @66
    @78
    @15
    @76
    @35
    @66
    @78
    wceq
    @76
    cB
    @77
    @5
    cR
    @23
    @8
    @11
    @10
    @13
    @20
    cX
    @19
    @28
    @25
    idomrootle.b
    @26
    @3
    @38
    @75
    @41
    adantr
    #
    @3
    @75
    simpr
    #
    @76
    cB
    @5
    cR
    @7
    @23
    c.ex
    @4
    cN
    @13
    @19
    @19
    @28
    @25
    idomrootle.b
    @26
    @80
    @81
    @76
    cB
    @5
    cR
    @23
    @13
    @4
    @19
    @28
    @48
    idomrootle.b
    @25
    @26
    @80
    @81
    evl1vard
    @49
    idomrootle.e
    @76
    @2
    @61
    @0
    @1
    @2
    @75
    simpl3
    #
    @62
    syl
    evl1expd
    @76
    @9
    cB
    @5
    cR
    @23
    @13
    cX
    @19
    @28
    @25
    idomrootle.b
    @51
    @26
    @80
    @0
    @1
    @2
    @75
    simpl2
    #
    @81
    evl1scad
    @54
    @77
    eqid
    #
    evl1subd
    simprd
    eqeq1d
    @76
    cR
    cgrp
    wcel
    #
    @20
    cB
    wcel
    #
    @1
    @79
    @21
    wb
    @3
    @85
    @75
    @3
    @37
    @85
    @42
    cR
    ringgrp
    syl
    adantr
    @76
    cR
    cmgp
    cfv
    #
    cmgm
    wcel
    #
    @2
    @75
    @86
    @76
    @87
    cmnd
    wcel
    #
    @88
    @3
    @89
    @75
    @3
    @37
    @89
    @42
    cR
    @87
    @87
    eqid
    #
    ringmgp
    syl
    adantr
    @87
    mndmgm
    syl
    @82
    @81
    cB
    c.ex
    @87
    cN
    @19
    cB
    cR
    @87
    @90
    idomrootle.b
    mgpbas
    idomrootle.e
    mulgnncl
    syl3anc
    @83
    cB
    cR
    @77
    @20
    cX
    @15
    idomrootle.b
    @29
    @84
    grpsubeq0
    syl3anc
    bitrd
    rabbidva
    eqtrd
    fveq2d
    @65
    3brtr3d
end
