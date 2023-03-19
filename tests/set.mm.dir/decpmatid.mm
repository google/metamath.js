include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "cn0.mm"
include "w3a.mm"
include "cdecpmat.mm"
include "co.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "weq.mm"
include "cc0.mm"
include "wceq.mm"
include "csca.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "cbs.mm"
include "pmatring.mm"
include "3adant3.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "simp3.mm"
include "decpmatval.mm"
include "syl2anc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2.mm"
include "pmat1ovd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "fvif.mm"
include "fveq1i.mm"
include "iffv.mm"
include "eqtri.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "ply1idvr1.mm"
include "3ad2ant2.mm"
include "eqcomd.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "0nn0.mm"
include "ply1moncl.mm"
include "mpan2.mm"
include "lmodvs1.mm"
include "cvv.mm"
include "cmpt.mm"
include "ply1sca.mm"
include "eqeltrd.mm"
include "a1i.mm"
include "coe1tm.mm"
include "syl3anc.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "adantl.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmptd.mm"
include "3eqtrd.mm"
include "csn.mm"
include "cxp.mm"
include "coe1z.mm"
include "fvconst2g.mm"
include "eqtrd.mm"
include "ifeq12d.mm"
include "3ad2ant1.mm"
include "syl5eq.mm"
include "mpt2eq3dva.mm"
include "wa.mm"
include "ifeq1d.mm"
include "mpt2eq3dv.mm"
include "iftrue.mm"
include "adantr.mm"
include "mat1.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "ifid.mm"
include "iffalse.mm"
include "3simpa.mm"
include "mat0op.mm"
include "pm2.61ian.mm"

theorem decpmatid
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let cK: class K
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume decpmatid.p: |- P = ( Poly1 ` R )
  assume decpmatid.c: |- C = ( N Mat P )
  assume decpmatid.i: |- I = ( 1r ` C )
  assume decpmatid.a: |- A = ( N Mat R )
  assume decpmatid.0: |- .0. = ( 0g ` A )
  assume decpmatid.1: |- .1. = ( 1r ` A )


  assert |- ( ( N e. Fin /\ R e. Ring /\ K e. NN0 ) -> ( I decompPMat K ) = if ( K = 0 , .1. , .0. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cK
    cn0
    wcel
    #
    w3a
    #
    cI
    cK
    cdecpmat
    co
    #
    vi
    vj
    cN
    cN
    cK
    vi
    cv
    #
    vj
    cv
    #
    cI
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    vi
    vj
    weq
    #
    cK
    cc0
    wceq
    #
    cP
    csca
    cfv
    #
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    @15
    cif
    #
    cmpt2
    #
    @12
    c.1
    c.0
    cif
    #
    @3
    cI
    cC
    cbs
    cfv
    #
    wcel
    #
    @2
    @4
    @10
    wceq
    @3
    cC
    crg
    wcel
    #
    @21
    @0
    @1
    @22
    @2
    cC
    cP
    cR
    cN
    decpmatid.p
    decpmatid.c
    pmatring
    3adant3
    @20
    cC
    cI
    @20
    eqid
    #
    decpmatid.i
    ringidcl
    syl
    @0
    @1
    @2
    simp3
    #
    cC
    @20
    cP
    vi
    vj
    cK
    cI
    cN
    decpmatid.c
    @23
    decpmatval
    syl2anc
    @3
    vi
    vj
    cN
    cN
    @9
    @17
    @3
    @5
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    w3a
    #
    @9
    cK
    @11
    cP
    cur
    cfv
    #
    cP
    c0g
    cfv
    #
    cif
    #
    cco1
    cfv
    #
    cfv
    #
    @17
    @27
    cK
    @8
    @31
    @27
    @7
    @30
    cco1
    @27
    cC
    cP
    cR
    cI
    @28
    @5
    @6
    cN
    @29
    decpmatid.p
    decpmatid.c
    @29
    eqid
    #
    @28
    eqid
    @0
    @1
    @2
    @25
    @26
    simp11
    @0
    @1
    @2
    @25
    @26
    simp12
    @3
    @25
    @26
    simp2
    @3
    @25
    @26
    simp3
    decpmatid.i
    pmat1ovd
    fveq2d
    fveq1d
    @27
    @32
    @11
    cK
    @28
    cco1
    cfv
    #
    cfv
    #
    cK
    @29
    cco1
    cfv
    #
    cfv
    #
    cif
    #
    @17
    @32
    cK
    @11
    @34
    @36
    cif
    #
    cfv
    @38
    cK
    @31
    @39
    @11
    @28
    @29
    cco1
    fvif
    fveq1i
    @11
    cK
    @34
    @36
    iffv
    eqtri
    @3
    @25
    @38
    @17
    wceq
    @26
    @3
    @11
    @35
    @16
    @37
    @15
    @3
    @35
    cK
    cc0
    cR
    cv1
    cfv
    #
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    cK
    @14
    @43
    cP
    cvsca
    cfv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    @16
    @3
    cK
    @34
    @44
    @3
    @28
    @43
    cco1
    @3
    @43
    @28
    @1
    @0
    @43
    @28
    wceq
    @2
    cP
    cR
    @42
    @41
    @40
    decpmatid.p
    @40
    eqid
    #
    @41
    eqid
    #
    @42
    eqid
    #
    ply1idvr1
    3ad2ant2
    eqcomd
    fveq2d
    fveq1d
    @3
    cK
    @44
    @47
    @3
    @43
    @46
    cco1
    @3
    @46
    @43
    @3
    cP
    clmod
    wcel
    #
    @43
    cP
    cbs
    cfv
    #
    wcel
    #
    @46
    @43
    wceq
    @1
    @0
    @51
    @2
    cP
    cR
    decpmatid.p
    ply1lmod
    3ad2ant2
    @1
    @0
    @53
    @2
    @1
    cc0
    cn0
    wcel
    #
    @53
    0nn0
    @52
    cc0
    cP
    cR
    @42
    @41
    @40
    decpmatid.p
    @48
    @49
    @50
    @52
    eqid
    #
    ply1moncl
    mpan2
    3ad2ant2
    @45
    @14
    @13
    @52
    cP
    @43
    @55
    @13
    eqid
    @45
    eqid
    #
    @14
    eqid
    lmodvs1
    syl2anc
    eqcomd
    fveq2d
    fveq1d
    @3
    vk
    cK
    vk
    cv
    #
    cc0
    wceq
    #
    @14
    @15
    cif
    #
    @16
    cn0
    @47
    cvv
    @3
    @1
    @14
    cR
    cbs
    cfv
    #
    wcel
    @54
    @47
    vk
    cn0
    @59
    cmpt
    wceq
    @0
    @1
    @2
    simp2
    @3
    @14
    cR
    cur
    cfv
    #
    @60
    @3
    @13
    cR
    cur
    @3
    cR
    @13
    @1
    @0
    cR
    @13
    wceq
    #
    @2
    cP
    cR
    crg
    decpmatid.p
    ply1sca
    3ad2ant2
    #
    eqcomd
    fveq2d
    @1
    @0
    @61
    @60
    wcel
    @2
    @60
    cR
    @61
    @60
    eqid
    #
    @61
    eqid
    #
    ringidcl
    3ad2ant2
    eqeltrd
    @54
    @3
    0nn0
    a1i
    vk
    @14
    cc0
    cP
    cR
    @45
    @42
    @60
    @41
    @40
    @15
    @15
    eqid
    #
    @64
    decpmatid.p
    @48
    @56
    @49
    @50
    coe1tm
    syl3anc
    @57
    cK
    wceq
    #
    @59
    @16
    wceq
    @3
    @67
    @58
    @12
    @14
    @15
    @57
    cK
    cc0
    eqeq1
    ifbid
    adantl
    @24
    @16
    cvv
    wcel
    @3
    @12
    @14
    @15
    @13
    cur
    fvex
    cR
    c0g
    fvex
    #
    ifex
    a1i
    fvmptd
    3eqtrd
    @3
    @37
    cK
    cn0
    @15
    csn
    cxp
    #
    cfv
    #
    @15
    @3
    cK
    @36
    @69
    @1
    @0
    @36
    @69
    wceq
    @2
    cP
    cR
    @15
    @29
    decpmatid.p
    @33
    @66
    coe1z
    3ad2ant2
    fveq1d
    @3
    @15
    cvv
    wcel
    #
    @2
    @70
    @15
    wceq
    @71
    @3
    @68
    a1i
    @24
    cn0
    @15
    cK
    cvv
    fvconst2g
    syl2anc
    eqtrd
    ifeq12d
    3ad2ant1
    syl5eq
    eqtrd
    mpt2eq3dva
    @12
    @3
    @18
    @19
    wceq
    @12
    @3
    wa
    #
    @18
    c.1
    @19
    @72
    vi
    vj
    cN
    cN
    @11
    @14
    @15
    cif
    #
    cmpt2
    vi
    vj
    cN
    cN
    @11
    @61
    @15
    cif
    #
    cmpt2
    #
    @18
    c.1
    @72
    vi
    vj
    cN
    cN
    @73
    @74
    @72
    @11
    @14
    @61
    @15
    @72
    @13
    cR
    cur
    @72
    cR
    @13
    @3
    @62
    @12
    @63
    adantl
    eqcomd
    fveq2d
    ifeq1d
    mpt2eq3dv
    @72
    vi
    vj
    cN
    cN
    @17
    @73
    @12
    @17
    @73
    wceq
    @3
    @12
    @11
    @16
    @14
    @15
    @12
    @14
    @15
    iftrue
    ifeq1d
    adantr
    mpt2eq3dv
    @3
    c.1
    @75
    wceq
    #
    @12
    @0
    @1
    @76
    @2
    @0
    @1
    wa
    #
    c.1
    cA
    cur
    cfv
    @75
    decpmatid.1
    cA
    cR
    @61
    vi
    vj
    cN
    @15
    decpmatid.a
    @65
    @66
    mat1
    syl5eq
    3adant3
    adantl
    3eqtr4d
    @12
    c.1
    @19
    wceq
    @3
    @12
    @19
    c.1
    @12
    c.1
    c.0
    iftrue
    eqcomd
    adantr
    eqtrd
    @12
    wn
    #
    @3
    wa
    #
    @18
    c.0
    @19
    @79
    vi
    vj
    cN
    cN
    @11
    @15
    @15
    cif
    #
    cmpt2
    vi
    vj
    cN
    cN
    @15
    cmpt2
    #
    @18
    c.0
    @79
    vi
    vj
    cN
    cN
    @80
    @15
    @80
    @15
    wceq
    @79
    @11
    @15
    ifid
    a1i
    mpt2eq3dv
    @79
    vi
    vj
    cN
    cN
    @17
    @80
    @79
    @11
    @16
    @15
    @15
    @78
    @16
    @15
    wceq
    @3
    @12
    @14
    @15
    iffalse
    adantr
    ifeq1d
    mpt2eq3dv
    @79
    @77
    c.0
    @81
    wceq
    @3
    @77
    @78
    @0
    @1
    @2
    3simpa
    adantl
    @77
    c.0
    cA
    c0g
    cfv
    @81
    decpmatid.0
    cA
    cR
    vi
    vj
    cN
    @15
    decpmatid.a
    @66
    mat0op
    syl5eq
    syl
    3eqtr4d
    @78
    c.0
    @19
    wceq
    @3
    @78
    @19
    c.0
    @12
    c.1
    c.0
    iffalse
    eqcomd
    adantr
    eqtrd
    pm2.61ian
    3eqtrd
end
