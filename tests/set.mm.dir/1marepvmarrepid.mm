include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cfv.mm"
include "cmarrep.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmat.mm"
include "cbs.mm"
include "cmatrepV.mm"
include "eqid.mm"
include "ma1repvcl.mm"
include "ancom2s.mm"
include "syl5eqel.mm"
include "wi.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "eleq2s.mm"
include "impcom.mm"
include "adantl.mm"
include "simpl.mm"
include "marrepval.mm"
include "syl22anc.mm"
include "w3a.mm"
include "iftrue.mm"
include "adantr.mm"
include "fveq2.mm"
include "sylan9eq.mm"
include "eqtr4d.mm"
include "wn.mm"
include "weq.mm"
include "cur.mm"
include "simpr.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "mat1ov.mm"
include "eqtr2.mm"
include "eqcomd.mm"
include "con3d.mm"
include "iffalse.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "pm2.61ian.mm"
include "mat1bas.mm"
include "3jca.mm"
include "3simpc.mm"
include "ma1repveval.mm"
include "ad2antlr.mm"
include "wb.mm"
include "equcom.mm"
include "a1i.mm"
include "ifbid.mm"
include "eqtr2d.mm"
include "ifeq2da.mm"
include "3eqtrd.mm"
include "mpt2eq3dva.mm"
include "marepvval.mm"
include "syl5req.mm"

theorem 1marepvmarrepid
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  assume marepvmarrep1.v: |- V = ( ( Base ` R ) ^m N )
  assume marepvmarrep1.o: |- .1. = ( 1r ` ( N Mat R ) )
  assume marepvmarrep1.x: |- X = ( ( .1. ( N matRepV R ) Z ) ` I )


  assert |- ( ( ( R e. Ring /\ N e. Fin ) /\ ( I e. N /\ Z e. V ) ) -> ( I ( X ( N matRRep R ) ( Z ` I ) ) I ) = X )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cI
    cN
    wcel
    #
    cZ
    cV
    wcel
    #
    wa
    #
    wa
    #
    cI
    cI
    cX
    cI
    cZ
    cfv
    #
    cN
    cR
    cmarrep
    co
    #
    co
    co
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cI
    wceq
    #
    vj
    cv
    #
    cI
    wceq
    #
    @7
    cR
    c0g
    cfv
    #
    cif
    #
    @10
    @12
    cX
    co
    #
    cif
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    @13
    @10
    cZ
    cfv
    #
    @10
    @12
    c.1
    co
    #
    cif
    #
    cmpt2
    #
    cX
    @6
    cX
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @7
    cR
    cbs
    cfv
    #
    wcel
    #
    @3
    @3
    @9
    @18
    wceq
    @6
    cX
    cI
    c.1
    cZ
    cN
    cR
    cmatrepV
    co
    #
    co
    cfv
    #
    @24
    marepvmarrep1.x
    @2
    @4
    @3
    @28
    @24
    wcel
    @23
    @24
    cZ
    cR
    c.1
    cI
    cN
    cV
    @23
    eqid
    #
    @24
    eqid
    #
    marepvmarrep1.v
    marepvmarrep1.o
    ma1repvcl
    ancom2s
    syl5eqel
    @5
    @26
    @2
    @4
    @3
    @26
    @3
    @26
    wi
    #
    cZ
    @25
    cN
    cmap
    co
    #
    cV
    cZ
    @32
    wcel
    cN
    @25
    cZ
    wf
    #
    @31
    cZ
    @25
    cN
    elmapi
    @33
    @3
    @26
    cN
    @25
    cI
    cZ
    ffvelrn
    ex
    syl
    marepvmarrep1.v
    eleq2s
    impcom
    adantl
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    #
    @34
    @23
    @24
    @8
    cR
    @7
    vi
    vj
    cI
    cI
    cX
    cN
    @14
    @29
    @30
    @8
    eqid
    @14
    eqid
    #
    marrepval
    syl22anc
    @6
    vi
    vj
    cN
    cN
    @17
    @21
    @11
    @6
    @10
    cN
    wcel
    #
    @12
    cN
    wcel
    #
    w3a
    #
    @17
    @21
    wceq
    @11
    @38
    wa
    #
    @17
    @15
    @21
    @11
    @17
    @15
    wceq
    @38
    @11
    @15
    @16
    iftrue
    adantr
    @13
    @39
    @15
    @21
    wceq
    @13
    @39
    wa
    @15
    @7
    @21
    @13
    @15
    @7
    wceq
    @39
    @13
    @7
    @14
    iftrue
    adantr
    @13
    @39
    @21
    @19
    @7
    @13
    @19
    @20
    iftrue
    @11
    @19
    @7
    wceq
    @38
    @10
    cI
    cZ
    fveq2
    adantr
    sylan9eq
    eqtr4d
    @13
    wn
    #
    @39
    wa
    #
    @20
    @14
    @21
    @15
    @41
    @20
    vi
    vj
    weq
    #
    cR
    cur
    cfv
    #
    @14
    cif
    #
    @14
    @39
    @20
    @44
    wceq
    #
    @40
    @38
    @45
    @11
    @38
    @23
    cR
    c.1
    @43
    @10
    @12
    cN
    @14
    @29
    @43
    eqid
    #
    @35
    @6
    @36
    @1
    @37
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    3ad2ant1
    #
    @6
    @36
    @0
    @37
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    3ad2ant1
    #
    @6
    @36
    @37
    simp2
    #
    @6
    @36
    @37
    simp3
    #
    marepvmarrep1.o
    mat1ov
    adantl
    adantl
    @41
    @42
    wn
    #
    @44
    @14
    wceq
    @39
    @40
    @51
    @11
    @40
    @51
    wi
    @38
    @11
    @42
    @13
    @11
    @42
    @13
    @11
    @42
    wa
    cI
    @12
    @10
    cI
    @12
    eqtr2
    eqcomd
    ex
    con3d
    adantr
    impcom
    @42
    @43
    @14
    iffalse
    syl
    eqtrd
    @40
    @21
    @20
    wceq
    @39
    @13
    @19
    @20
    iffalse
    adantr
    @40
    @15
    @14
    wceq
    @39
    @13
    @7
    @14
    iffalse
    adantr
    3eqtr4rd
    pm2.61ian
    eqtrd
    @11
    wn
    #
    @38
    wa
    #
    @17
    @16
    @13
    @19
    vj
    vi
    weq
    #
    @43
    @14
    cif
    #
    cif
    #
    @21
    @52
    @17
    @16
    wceq
    @38
    @11
    @15
    @16
    iffalse
    adantr
    @53
    @0
    c.1
    @24
    wcel
    #
    @4
    @3
    w3a
    #
    @36
    @37
    wa
    #
    w3a
    #
    @16
    @56
    wceq
    @38
    @60
    @52
    @38
    @0
    @58
    @59
    @48
    @6
    @36
    @58
    @37
    @6
    @57
    @4
    @3
    @2
    @57
    @5
    @23
    @24
    cR
    c.1
    cN
    @29
    @30
    marepvmarrep1.o
    mat1bas
    adantr
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    @34
    3jca
    #
    3ad2ant1
    @6
    @36
    @37
    3simpc
    3jca
    adantl
    @23
    @24
    cZ
    cR
    c.1
    cX
    @10
    @12
    cI
    c.1
    cN
    cV
    @14
    @29
    @30
    marepvmarrep1.v
    marepvmarrep1.o
    @35
    marepvmarrep1.x
    ma1repveval
    syl
    @53
    @13
    @55
    @20
    @19
    @53
    @40
    wa
    #
    @20
    @44
    @55
    @62
    @23
    cR
    c.1
    @43
    @10
    @12
    cN
    @14
    @29
    @46
    @35
    @38
    @1
    @52
    @40
    @47
    ad2antlr
    @38
    @0
    @52
    @40
    @48
    ad2antlr
    @38
    @36
    @52
    @40
    @49
    ad2antlr
    @38
    @37
    @52
    @40
    @50
    ad2antlr
    marepvmarrep1.o
    mat1ov
    @62
    @42
    @54
    @43
    @14
    @42
    @54
    wb
    @62
    vi
    vj
    equcom
    a1i
    ifbid
    eqtr2d
    ifeq2da
    3eqtrd
    pm2.61ian
    mpt2eq3dva
    @6
    cX
    @28
    @22
    marepvmarrep1.x
    @6
    @58
    @28
    @22
    wceq
    @61
    @23
    @24
    cZ
    @27
    cR
    vi
    vj
    cI
    c.1
    cN
    cV
    @29
    @30
    @27
    eqid
    marepvmarrep1.v
    marepvval
    syl
    syl5req
    3eqtrd
end
