include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cif.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "clgs.mm"
include "co.mm"
include "cpc.mm"
include "cexp.mm"
include "cmpt.mm"
include "cseq.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "neg1mulneg1e1.mm"
include "syl6eq.mm"
include "ax-1cn.mm"
include "mulm1i.mm"
include "ifsb.mm"
include "simpr.mm"
include "biantrud.mm"
include "ifbid.mm"
include "oveq2d.mm"
include "wn.mm"
include "cle.mm"
include "cr.mm"
include "wb.mm"
include "simpl2.mm"
include "zred.mm"
include "0re.mm"
include "ltlen.mm"
include "sylancl.mm"
include "simpl3.mm"
include "necomd.mm"
include "bitr4d.mm"
include "le0neg1d.mm"
include "renegcld.mm"
include "lenlt.mm"
include "sylancr.mm"
include "3bitrd.mm"
include "ifnot.mm"
include "3eqtr3a.mm"
include "3eqtrd.mm"
include "1t1e1.mm"
include "iffalse.mm"
include "intnand.mm"
include "iffalsed.mm"
include "oveq12d.mm"
include "3eqtr4a.mm"
include "pm2.61dan.mm"
include "eqcomd.mm"
include "cq.mm"
include "zq.mm"
include "syl.mm"
include "pcneg.mm"
include "syl2anc.mm"
include "ifeq1da.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "absnegd.mm"
include "fveq12d.mm"
include "neg1cn.mm"
include "keepel.mm"
include "a1i.mm"
include "cuz.mm"
include "nnabscl.mm"
include "3adant1.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf.mm"
include "cfz.mm"
include "eqid.mm"
include "lgsfcl3.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "zmulcl.mm"
include "seqcl.mm"
include "zcnd.mm"
include "mulassd.mm"
include "eqtrd.mm"
include "simp1.mm"
include "znegcl.mm"
include "simp3.mm"
include "negne0d.mm"
include "lgsval4.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem lgsneg
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p


  assert |- ( ( A e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> ( A /L -u N ) = ( if ( A < 0 , -u 1 , 1 ) x. ( A /L N ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    w3a
    #
    cN
    cneg
    #
    cc0
    clt
    wbr
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    c1
    cneg
    #
    c1
    cif
    #
    @4
    cabs
    cfv
    #
    cmul
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    cA
    @11
    clgs
    co
    #
    @11
    @4
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    #
    @6
    @8
    c1
    cif
    #
    cN
    cc0
    clt
    wbr
    #
    @6
    wa
    #
    @8
    c1
    cif
    #
    cN
    cabs
    cfv
    #
    cmul
    vn
    cn
    @12
    @13
    @11
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cA
    @4
    clgs
    co
    #
    @21
    cA
    cN
    clgs
    co
    #
    cmul
    co
    @3
    @20
    @21
    @24
    cmul
    co
    #
    @31
    cmul
    co
    @33
    @3
    @9
    @36
    @19
    @31
    cmul
    @3
    @36
    @9
    @3
    @6
    @36
    @9
    wceq
    @3
    @6
    wa
    #
    @36
    @8
    @24
    cmul
    co
    #
    @5
    @8
    c1
    cif
    #
    @9
    @37
    @21
    @8
    @24
    cmul
    @6
    @21
    @8
    wceq
    @3
    @6
    @8
    c1
    iftrue
    adantl
    oveq1d
    @37
    @8
    @22
    @8
    c1
    cif
    #
    cmul
    co
    #
    @22
    c1
    @8
    cif
    #
    @38
    @39
    @22
    @8
    c1
    @41
    c1
    @8
    @40
    @8
    wceq
    @41
    @8
    @8
    cmul
    co
    c1
    @40
    @8
    @8
    cmul
    oveq2
    neg1mulneg1e1
    syl6eq
    @40
    c1
    wceq
    @41
    @8
    c1
    cmul
    co
    @8
    @40
    c1
    @8
    cmul
    oveq2
    c1
    ax-1cn
    mulm1i
    syl6eq
    ifsb
    @37
    @40
    @24
    @8
    cmul
    @37
    @22
    @23
    @8
    c1
    @37
    @6
    @22
    @3
    @6
    simpr
    #
    biantrud
    ifbid
    oveq2d
    @37
    @42
    @5
    wn
    #
    c1
    @8
    cif
    @39
    @37
    @22
    @44
    c1
    @8
    @37
    @22
    cN
    cc0
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @44
    @37
    @22
    @45
    cc0
    cN
    wne
    #
    wa
    #
    @45
    @37
    cN
    cr
    wcel
    cc0
    cr
    wcel
    #
    @22
    @48
    wb
    @37
    cN
    @0
    @1
    @2
    @6
    simpl2
    zred
    #
    0re
    cN
    cc0
    ltlen
    sylancl
    @37
    @47
    @45
    @37
    cN
    cc0
    @0
    @1
    @2
    @6
    simpl3
    necomd
    biantrud
    bitr4d
    @37
    cN
    @50
    le0neg1d
    @37
    @49
    @4
    cr
    wcel
    @46
    @44
    wb
    0re
    @37
    cN
    @50
    renegcld
    cc0
    @4
    lenlt
    sylancr
    3bitrd
    ifbid
    @5
    c1
    @8
    ifnot
    syl6eq
    3eqtr3a
    @37
    @5
    @7
    @8
    c1
    @37
    @6
    @5
    @43
    biantrud
    ifbid
    3eqtrd
    @3
    @6
    wn
    #
    wa
    #
    c1
    c1
    cmul
    co
    c1
    @36
    @9
    1t1e1
    @52
    @21
    c1
    @24
    c1
    cmul
    @51
    @21
    c1
    wceq
    @3
    @6
    @8
    c1
    iffalse
    adantl
    @52
    @23
    @8
    c1
    @52
    @6
    @22
    @3
    @51
    simpr
    #
    intnand
    iffalsed
    oveq12d
    @52
    @7
    @8
    c1
    @52
    @6
    @5
    @53
    intnand
    iffalsed
    3eqtr4a
    pm2.61dan
    eqcomd
    @3
    @10
    @25
    @18
    @30
    @3
    @17
    @29
    cmul
    c1
    @3
    vn
    cn
    @16
    @28
    @3
    @12
    @15
    @27
    c1
    @3
    @12
    wa
    #
    @14
    @26
    @13
    cexp
    @54
    @12
    cN
    cq
    wcel
    #
    @14
    @26
    wceq
    @3
    @12
    simpr
    @54
    @1
    @55
    @0
    @1
    @2
    @12
    simpl2
    cN
    zq
    syl
    cN
    @11
    pcneg
    syl2anc
    oveq2d
    ifeq1da
    mpteq2dv
    seqeq3d
    @3
    cN
    @1
    @0
    cN
    cc
    wcel
    @2
    cN
    zcn
    3ad2ant2
    #
    absnegd
    fveq12d
    oveq12d
    @3
    @21
    @24
    @31
    @21
    cc
    wcel
    @3
    @6
    @8
    c1
    cc
    neg1cn
    ax-1cn
    keepel
    a1i
    @24
    cc
    wcel
    @3
    @23
    @8
    c1
    cc
    neg1cn
    ax-1cn
    keepel
    a1i
    @3
    @31
    @3
    vx
    vy
    cmul
    cz
    @29
    c1
    @25
    @3
    @25
    cn
    c1
    cuz
    cfv
    @1
    @2
    @25
    cn
    wcel
    @0
    cN
    nnabscl
    3adant1
    nnuz
    syl6eleq
    @3
    cn
    cz
    @29
    wf
    vx
    cv
    #
    cn
    wcel
    @57
    @29
    cfv
    cz
    wcel
    @57
    c1
    @25
    cfz
    co
    wcel
    cA
    vn
    @29
    cN
    @29
    eqid
    #
    lgsfcl3
    @57
    @25
    elfznn
    cn
    cz
    @57
    @29
    ffvelrn
    syl2an
    @57
    cz
    wcel
    vy
    cv
    #
    cz
    wcel
    wa
    @57
    @59
    cmul
    co
    cz
    wcel
    @3
    @57
    @59
    zmulcl
    adantl
    seqcl
    zcnd
    mulassd
    eqtrd
    @3
    @0
    @4
    cz
    wcel
    #
    @4
    cc0
    wne
    @34
    @20
    wceq
    @0
    @1
    @2
    simp1
    @1
    @0
    @60
    @2
    cN
    znegcl
    3ad2ant2
    @3
    cN
    @56
    @0
    @1
    @2
    simp3
    negne0d
    cA
    vn
    @17
    @4
    @17
    eqid
    lgsval4
    syl3anc
    @3
    @35
    @32
    @21
    cmul
    cA
    vn
    @29
    cN
    @58
    lgsval4
    oveq2d
    3eqtr4d
end
