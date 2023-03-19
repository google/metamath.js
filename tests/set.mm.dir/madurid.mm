include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cfv.mm"
include "cotp.mm"
include "cmmul.mm"
include "co.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cbs.mm"
include "eqid.mm"
include "simpr.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "cxp.mm"
include "cmap.mm"
include "matbas2i.mm"
include "wf.mm"
include "maduf.mm"
include "adantl.mm"
include "simpl.mm"
include "ffvelrnd.mm"
include "syl.mm"
include "mamuval.mm"
include "wceq.mm"
include "matmulr.mm"
include "sylan.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp1r.mm"
include "elmapi.mm"
include "3ad2ant1.mm"
include "simpl2.mm"
include "fovrnd.mm"
include "simp3.mm"
include "madugsum.mm"
include "iftrue.mm"
include "wfn.mm"
include "ffn.mm"
include "fnov.mm"
include "sylib.mm"
include "equtr2.mm"
include "oveq1d.mm"
include "ifeq1da.mm"
include "ifid.mm"
include "syl6eq.mm"
include "mpt2eq3dv.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "3ad2antl1.mm"
include "wn.mm"
include "simpl1r.mm"
include "ad2antrr.mm"
include "simpll2.mm"
include "fovrnda.mm"
include "3impb.mm"
include "simpl3.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "necomd.mm"
include "mdetralt2.mm"
include "oveq1.mm"
include "syl5eqr.mm"
include "ifeq2d.mm"
include "iffalse.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"
include "eqtrd.mm"
include "mpt2eq3dva.mm"
include "cur.mm"
include "oveq2i.mm"
include "crg.mm"
include "crngring.mm"
include "mdetf.mm"
include "matsc.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"

theorem madurid
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.1: class .1.
  let cJ: class J
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume madurid.a: |- A = ( N Mat R )
  assume madurid.b: |- B = ( Base ` A )
  assume madurid.j: |- J = ( N maAdju R )
  assume madurid.d: |- D = ( N maDet R )
  assume madurid.i: |- .1. = ( 1r ` A )
  assume madurid.t: |- .x. = ( .r ` A )
  assume madurid.s: |- .xb = ( .s ` A )


  assert |- ( ( M e. B /\ R e. CRing ) -> ( M .x. ( J ` M ) ) = ( ( D ` M ) .xb .1. ) )

  proof
    cM
    cB
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cM
    cM
    cJ
    cfv
    #
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    va
    vb
    cN
    cN
    cR
    vc
    cN
    va
    cv
    #
    vc
    cv
    #
    cM
    co
    #
    @6
    vb
    cv
    #
    @3
    co
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    cmpt2
    #
    cM
    @3
    c.x
    co
    cM
    cD
    cfv
    #
    c.1
    c.xb
    co
    #
    @2
    cR
    cbs
    cfv
    #
    cN
    cR
    @9
    va
    vc
    vb
    @4
    cN
    cN
    ccrg
    cM
    @3
    @4
    eqid
    #
    @14
    eqid
    #
    @9
    eqid
    #
    @0
    @1
    simpr
    @0
    cN
    cfn
    wcel
    #
    @1
    @0
    @18
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    madurid.a
    madurid.b
    matrcl
    simpld
    #
    adantr
    #
    @20
    @20
    @0
    cM
    @14
    cN
    cN
    cxp
    #
    cmap
    co
    #
    wcel
    #
    @1
    cA
    cB
    cR
    @14
    cM
    cN
    madurid.a
    @16
    madurid.b
    matbas2i
    adantr
    #
    @2
    @3
    cB
    wcel
    @3
    @22
    wcel
    @2
    cB
    cB
    cM
    cJ
    @1
    cB
    cB
    cJ
    wf
    @0
    cA
    cB
    cR
    cJ
    cN
    madurid.a
    madurid.j
    madurid.b
    maduf
    adantl
    @0
    @1
    simpl
    #
    ffvelrnd
    cA
    cB
    cR
    @14
    @3
    cN
    madurid.a
    @16
    madurid.b
    matbas2i
    syl
    mamuval
    @2
    @4
    c.x
    cM
    @3
    @2
    @4
    cA
    cmulr
    cfv
    #
    c.x
    @0
    @18
    @1
    @4
    @26
    wceq
    @19
    cA
    cR
    @4
    cN
    ccrg
    madurid.a
    @15
    matmulr
    sylan
    madurid.t
    syl6eqr
    oveqd
    @2
    @11
    va
    vb
    cN
    cN
    va
    vb
    weq
    #
    @12
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt2
    #
    @13
    @2
    va
    vb
    cN
    cN
    @10
    @29
    @2
    @5
    cN
    wcel
    #
    @8
    cN
    wcel
    #
    w3a
    #
    @10
    vd
    vc
    cN
    cN
    vd
    vb
    weq
    #
    @7
    vd
    cv
    #
    @6
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    @29
    @33
    cA
    cB
    cD
    cR
    @9
    vc
    vd
    cJ
    @14
    @8
    cM
    cN
    @7
    madurid.a
    madurid.j
    madurid.b
    madurid.d
    @17
    @16
    @0
    @1
    @31
    @32
    simp1l
    @0
    @1
    @31
    @32
    simp1r
    @33
    @6
    cN
    wcel
    #
    wa
    @5
    @6
    @14
    cN
    cN
    cM
    @33
    @21
    @14
    cM
    wf
    #
    @40
    @2
    @31
    @41
    @32
    @2
    @23
    @41
    @24
    cM
    @14
    @21
    elmapi
    syl
    #
    3ad2ant1
    #
    adantr
    @2
    @31
    @32
    @40
    simpl2
    @33
    @40
    simpr
    fovrnd
    @2
    @31
    @32
    simp3
    madugsum
    @33
    @27
    @39
    @29
    wceq
    #
    @2
    @31
    @27
    @44
    @32
    @2
    @27
    wa
    #
    @29
    @12
    @39
    @27
    @29
    @12
    wceq
    @2
    @27
    @12
    @28
    iftrue
    adantl
    @45
    cM
    @38
    cD
    @45
    cM
    vd
    vc
    cN
    cN
    @36
    cmpt2
    #
    @38
    @2
    cM
    @46
    wceq
    #
    @27
    @2
    cM
    @21
    wfn
    #
    @47
    @2
    @41
    @48
    @42
    @21
    @14
    cM
    ffn
    syl
    vd
    vc
    cN
    cN
    cM
    fnov
    sylib
    adantr
    @45
    vd
    vc
    cN
    cN
    @37
    @36
    @27
    @37
    @36
    wceq
    @2
    @27
    @37
    @34
    @36
    @36
    cif
    @36
    @27
    @34
    @7
    @36
    @36
    @27
    @34
    wa
    @5
    @35
    @6
    cM
    va
    vd
    vb
    equtr2
    oveq1d
    ifeq1da
    @34
    @36
    ifid
    syl6eq
    adantl
    mpt2eq3dv
    eqtr4d
    fveq2d
    eqtr2d
    3ad2antl1
    @33
    @27
    wn
    #
    wa
    #
    vd
    vc
    cN
    cN
    @34
    @7
    vd
    va
    weq
    #
    @7
    @36
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    @28
    @39
    @29
    @50
    cD
    cR
    vd
    vc
    @8
    @5
    @14
    cN
    @7
    @36
    @28
    madurid.d
    @16
    @28
    eqid
    #
    @0
    @1
    @31
    @32
    @49
    simpl1r
    @33
    @18
    @49
    @2
    @31
    @18
    @32
    @20
    3ad2ant1
    adantr
    @50
    @40
    wa
    @5
    @6
    @14
    cN
    cN
    cM
    @33
    @41
    @49
    @40
    @43
    ad2antrr
    @2
    @31
    @32
    @49
    @40
    simpll2
    @50
    @40
    simpr
    fovrnd
    @50
    @35
    cN
    wcel
    @40
    @36
    @14
    wcel
    @50
    @35
    @6
    @14
    cN
    cN
    cM
    @33
    @41
    @49
    @43
    adantr
    fovrnda
    3impb
    @2
    @31
    @32
    @49
    simpl3
    @2
    @31
    @32
    @49
    simpl2
    @49
    @8
    @5
    wne
    @33
    @49
    @5
    @8
    @5
    @8
    wne
    @49
    @5
    @8
    df-ne
    biimpri
    necomd
    adantl
    mdetralt2
    @50
    @38
    @54
    cD
    @50
    vd
    vc
    cN
    cN
    @37
    @53
    @50
    @34
    @36
    @52
    @7
    @50
    @36
    @51
    @36
    @36
    cif
    @52
    @51
    @36
    ifid
    @50
    @51
    @36
    @7
    @36
    @51
    @36
    @7
    wceq
    @50
    @35
    @5
    @6
    cM
    oveq1
    adantl
    ifeq1da
    syl5eqr
    ifeq2d
    mpt2eq3dv
    fveq2d
    @49
    @29
    @28
    wceq
    @33
    @27
    @12
    @28
    iffalse
    adantl
    3eqtr4d
    pm2.61dan
    eqtrd
    mpt2eq3dva
    @2
    @13
    @12
    cA
    cur
    cfv
    #
    c.xb
    co
    #
    @30
    c.1
    @56
    @12
    c.xb
    madurid.i
    oveq2i
    @2
    @18
    cR
    crg
    wcel
    #
    @12
    @14
    wcel
    @57
    @30
    wceq
    @20
    @1
    @58
    @0
    cR
    crngring
    adantl
    @2
    cB
    @14
    cM
    cD
    @1
    cB
    @14
    cD
    wf
    @0
    cA
    cB
    cD
    cR
    @14
    cN
    madurid.d
    madurid.a
    madurid.b
    @16
    mdetf
    adantl
    @25
    ffvelrnd
    cA
    cR
    c.xb
    va
    vb
    @14
    @12
    cN
    @28
    madurid.a
    @16
    madurid.s
    @55
    matsc
    syl3anc
    syl5eq
    eqtr4d
    3eqtr3d
end
