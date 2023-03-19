include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cn0.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmpt.mm"
include "cn.mm"
include "cdvds.mm"
include "cif.mm"
include "wceq.mm"
include "wcel.mm"
include "cc.mm"
include "2cn.mm"
include "nn0cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "syl.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "breq1i.mm"
include "wb.mm"
include "wtru.mm"
include "cr.mm"
include "neg1rr.mm"
include "reexpcl.mm"
include "mpan.mm"
include "2nn0.mm"
include "nn0mulcl.mm"
include "nn0p1nn.mm"
include "nndivred.mm"
include "recnd.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "iserodd.mm"
include "trud.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "addid2.mm"
include "0cnd.mm"
include "1eluzge0.mm"
include "a1i.mm"
include "1nn0.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "ioran.mm"
include "leibpilem1.mm"
include "simprd.mm"
include "simpld.mm"
include "sylan2b.mm"
include "ifclda.mm"
include "fmpti.mm"
include "ffvelrni.mm"
include "mp1i.mm"
include "cfz.mm"
include "simpr.mm"
include "1m1e0.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "elfz1eq.mm"
include "fveq2d.mm"
include "0nn0.mm"
include "iftrue.mm"
include "orcs.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "syl6eq.mm"
include "seqid.mm"
include "1zzd.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "nnne0.mm"
include "neneqd.mm"
include "biorf.mm"
include "ifbid.mm"
include "breq2.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "ifex.mm"
include "nnnn0.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "3eqtr4d.mm"
include "seqfeq.mm"
include "eqtr4d.mm"
include "cz.mm"
include "cvv.mm"
include "1z.mm"
include "seqex.mm"
include "climres.mm"
include "mp2an.mm"
include "bitr3i.mm"
include "3bitri.mm"

theorem leibpilem2
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vx: setvar x
  let cN: class N
  assume leibpi.1: |- F = ( n e. NN0 |-> ( ( -u 1 ^ n ) / ( ( 2 x. n ) + 1 ) ) )
  assume leibpilem2.2: |- G = ( k e. NN0 |-> if ( ( k = 0 \/ 2 || k ) , 0 , ( ( -u 1 ^ ( ( k - 1 ) / 2 ) ) / k ) ) )
  assume leibpilem2.3: |- A e. _V

  disjoint k n
  disjoint G n
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint k x
  disjoint n x
  disjoint N n
  assert |- ( seq 0 ( + , F ) ~~> A <-> seq 0 ( + , G ) ~~> A )

  proof
    caddc
    cF
    cc0
    cseq
    #
    cA
    cli
    wbr
    caddc
    vn
    cn0
    c1
    cneg
    #
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    @4
    cdiv
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    cA
    cli
    wbr
    #
    caddc
    vk
    cn
    c2
    vk
    cv
    #
    cdvds
    wbr
    #
    cc0
    @1
    @12
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    @12
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    c1
    cseq
    #
    cA
    cli
    wbr
    #
    caddc
    cG
    cc0
    cseq
    #
    cA
    cli
    wbr
    #
    @0
    @10
    cA
    cli
    cF
    @9
    wceq
    @0
    @10
    wceq
    cF
    vn
    cn0
    @1
    @2
    cexp
    co
    #
    @4
    cdiv
    co
    #
    cmpt
    @9
    leibpi.1
    vn
    cn0
    @8
    @25
    @2
    cn0
    wcel
    #
    @7
    @24
    @4
    cdiv
    @26
    @6
    @2
    @1
    cexp
    @26
    @6
    @3
    c2
    cdiv
    co
    #
    @2
    @26
    @5
    @3
    c2
    cdiv
    @26
    @3
    cc
    wcel
    #
    c1
    cc
    wcel
    @5
    @3
    wceq
    @26
    c2
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @28
    2cn
    @2
    nn0cn
    #
    c2
    @2
    mulcl
    sylancr
    ax-1cn
    @3
    c1
    pncan
    sylancl
    oveq1d
    @26
    @30
    @27
    @2
    wceq
    #
    @31
    @30
    @29
    c2
    cc0
    wne
    @32
    2cn
    2ne0
    @2
    c2
    divcan3
    mp3an23
    syl
    eqtrd
    oveq2d
    oveq1d
    #
    mpteq2ia
    eqtr4i
    caddc
    cF
    @9
    cc0
    seqeq3
    ax-mp
    breq1i
    @11
    @21
    wb
    wtru
    cA
    @17
    @8
    vn
    vk
    @26
    @8
    cc
    wcel
    wtru
    @26
    @8
    @25
    cc
    @33
    @26
    @25
    @26
    @24
    @4
    @1
    cr
    wcel
    #
    @26
    @24
    cr
    wcel
    neg1rr
    @1
    @2
    reexpcl
    mpan
    @26
    @3
    cn0
    wcel
    #
    @4
    cn
    wcel
    c2
    cn0
    wcel
    @26
    @35
    2nn0
    c2
    @2
    nn0mulcl
    mpan
    @3
    nn0p1nn
    syl
    nndivred
    recnd
    eqeltrd
    adantl
    @12
    @4
    wceq
    #
    @16
    @7
    @12
    @4
    cdiv
    @36
    @15
    @6
    @1
    cexp
    @36
    @14
    @5
    c2
    cdiv
    @12
    @4
    c1
    cmin
    oveq1
    oveq1d
    oveq2d
    @36
    id
    oveq12d
    iserodd
    trud
    @21
    @22
    c1
    cuz
    cfv
    #
    cres
    #
    cA
    cli
    wbr
    #
    @23
    @38
    @20
    cA
    cli
    @38
    @20
    wceq
    wtru
    @38
    caddc
    cG
    c1
    cseq
    @20
    wtru
    vn
    caddc
    cc
    cG
    cc0
    c1
    cc0
    @30
    cc0
    @2
    caddc
    co
    @2
    wceq
    wtru
    @2
    addid2
    adantl
    wtru
    0cnd
    c1
    cc0
    cuz
    cfv
    wcel
    wtru
    1eluzge0
    a1i
    c1
    cn0
    wcel
    c1
    cG
    cfv
    cc
    wcel
    wtru
    1nn0
    cn0
    cc
    c1
    cG
    vk
    cn0
    cc
    @12
    cc0
    wceq
    #
    @13
    wo
    #
    cc0
    @17
    cif
    #
    cG
    leibpilem2.2
    @12
    cn0
    wcel
    #
    @41
    cc0
    @17
    cc
    @43
    @41
    wa
    0cnd
    @41
    wn
    @43
    @40
    wn
    @13
    wn
    wa
    #
    @17
    cc
    wcel
    @40
    @13
    ioran
    @43
    @44
    wa
    #
    @17
    @45
    @16
    @12
    @45
    @34
    @15
    cn0
    wcel
    #
    @16
    cr
    wcel
    neg1rr
    @45
    @12
    cn
    wcel
    #
    @46
    @12
    leibpilem1
    #
    simprd
    @1
    @15
    reexpcl
    sylancr
    @45
    @47
    @46
    @48
    simpld
    nndivred
    recnd
    sylan2b
    ifclda
    fmpti
    ffvelrni
    mp1i
    wtru
    @2
    cc0
    c1
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @2
    cG
    cfv
    #
    cc0
    cG
    cfv
    #
    cc0
    @52
    @2
    cc0
    cG
    @52
    @2
    cc0
    cc0
    cfz
    co
    #
    wcel
    @2
    cc0
    wceq
    #
    @52
    @2
    @50
    @55
    wtru
    @51
    simpr
    @49
    cc0
    cc0
    cfz
    1m1e0
    oveq2i
    syl6eleq
    @2
    cc0
    elfz1eq
    syl
    fveq2d
    cc0
    cn0
    wcel
    @54
    cc0
    wceq
    0nn0
    vk
    cc0
    @42
    cc0
    cn0
    cG
    @40
    @13
    @42
    cc0
    wceq
    @41
    cc0
    @17
    iftrue
    orcs
    leibpilem2.2
    c0ex
    fvmpt
    ax-mp
    syl6eq
    seqid
    wtru
    caddc
    vn
    @19
    cG
    c1
    wtru
    1zzd
    wtru
    @2
    @37
    wcel
    #
    wa
    #
    @2
    cn
    wcel
    #
    @2
    @19
    cfv
    #
    @53
    wceq
    @58
    @2
    @37
    cn
    wtru
    @57
    simpr
    nnuz
    syl6eleqr
    @59
    c2
    @2
    cdvds
    wbr
    #
    cc0
    @1
    @2
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    @2
    cdiv
    co
    #
    cif
    #
    @56
    @61
    wo
    #
    cc0
    @65
    cif
    #
    @60
    @53
    @59
    @61
    @67
    cc0
    @65
    @59
    @56
    wn
    @61
    @67
    wb
    @59
    @2
    cc0
    @2
    nnne0
    neneqd
    @56
    @61
    biorf
    syl
    ifbid
    vk
    @2
    @18
    @66
    cn
    @19
    @12
    @2
    wceq
    #
    @13
    @61
    @17
    @65
    cc0
    @12
    @2
    c2
    cdvds
    breq2
    #
    @69
    @16
    @64
    @12
    @2
    cdiv
    @69
    @15
    @63
    @1
    cexp
    @69
    @14
    @62
    c2
    cdiv
    @12
    @2
    c1
    cmin
    oveq1
    oveq1d
    oveq2d
    @69
    id
    oveq12d
    #
    ifbieq2d
    @19
    eqid
    @61
    cc0
    @65
    c0ex
    @64
    @2
    cdiv
    ovex
    #
    ifex
    fvmpt
    @59
    @26
    @53
    @68
    wceq
    @2
    nnnn0
    vk
    @2
    @42
    @68
    cn0
    cG
    @69
    @41
    @67
    @17
    @65
    cc0
    @69
    @40
    @56
    @13
    @61
    @12
    @2
    cc0
    eqeq1
    @70
    orbi12d
    @71
    ifbieq2d
    leibpilem2.2
    @67
    cc0
    @65
    c0ex
    @72
    ifex
    fvmpt
    syl
    3eqtr4d
    syl
    seqfeq
    eqtr4d
    trud
    breq1i
    c1
    cz
    wcel
    @22
    cvv
    wcel
    @39
    @23
    wb
    1z
    caddc
    cG
    cc0
    seqex
    cA
    @22
    c1
    cvv
    climres
    mp2an
    bitr3i
    3bitri
end
