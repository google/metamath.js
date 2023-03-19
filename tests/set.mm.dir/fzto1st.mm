include "wcel.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "elfz1b.mm"
include "biimpi.mm"
include "eleq2s.mm"
include "3ancoma.mm"
include "sylibr.mm"
include "wa.mm"
include "df-3an.mm"
include "cv.mm"
include "wceq.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "wi.mm"
include "cid.mm"
include "cres.mm"
include "caddc.mm"
include "breq1.mm"
include "simpl.mm"
include "breq2d.mm"
include "ifbid.mm"
include "ifeq12d.mm"
include "mpteq2dva.mm"
include "eqid.mm"
include "fzto1st1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "syl6eqr.mm"
include "cbs.mm"
include "cfv.mm"
include "cfn.mm"
include "fzfi.mm"
include "eqeltri.mm"
include "idresperm.mm"
include "eleqtrri.mm"
include "2a1i.mm"
include "cpr.mm"
include "cpmtr.mm"
include "ccom.mm"
include "simplr.mm"
include "peano2nnd.mm"
include "simpll.mm"
include "simpr.mm"
include "3jca.mm"
include "syl6eleqr.mm"
include "psgnfzto1stlem.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "crn.mm"
include "symgtrf.mm"
include "pmtrto1cl.mm"
include "sseldi.mm"
include "nnred.mm"
include "1red.mm"
include "readdcld.mm"
include "lep1d.mm"
include "letrd.mm"
include "mpd.mm"
include "cplusg.mm"
include "symgov.mm"
include "symgcl.mm"
include "eqeltrrd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "nnindd.mm"
include "imp.mm"
include "sylbi.mm"
include "syl.mm"

theorem fzto1st
  let cB: class B
  let cD: class D
  let cP: class P
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cN: class N
  let vx: setvar x
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  assume psgnfzto1st.d: |- D = ( 1 ... N )
  assume psgnfzto1st.p: |- P = ( i e. D |-> if ( i = 1 , I , if ( i <_ I , ( i - 1 ) , i ) ) )
  assume psgnfzto1st.g: |- G = ( SymGrp ` D )
  assume psgnfzto1st.b: |- B = ( Base ` G )

  disjoint D i
  disjoint I i
  disjoint N i
  disjoint B i
  disjoint D x
  disjoint i x
  disjoint K i
  disjoint K x
  disjoint B m
  disjoint B n
  disjoint i m
  disjoint m n
  disjoint i n
  disjoint D m
  disjoint D n
  disjoint I m
  disjoint N m
  disjoint N n
  disjoint P m
  assert |- ( I e. D -> P e. B )

  proof
    cI
    cD
    wcel
    #
    cN
    cn
    wcel
    #
    cI
    cn
    wcel
    #
    cI
    cN
    cle
    wbr
    #
    w3a
    #
    cP
    cB
    wcel
    #
    @0
    @2
    @1
    @3
    w3a
    #
    @4
    @6
    cI
    c1
    cN
    cfz
    co
    #
    cD
    cI
    @7
    wcel
    @6
    cN
    cI
    elfz1b
    biimpi
    psgnfzto1st.d
    eleq2s
    @1
    @2
    @3
    3ancoma
    sylibr
    @4
    @1
    @2
    wa
    #
    @3
    wa
    @5
    @1
    @2
    @3
    df-3an
    @8
    @3
    @5
    @1
    vm
    cv
    #
    cN
    cle
    wbr
    #
    vi
    cD
    vi
    cv
    #
    c1
    wceq
    #
    @9
    @11
    @9
    cle
    wbr
    #
    @11
    c1
    cmin
    co
    #
    @11
    cif
    #
    cif
    #
    cmpt
    #
    cB
    wcel
    #
    wi
    c1
    cN
    cle
    wbr
    #
    cid
    cD
    cres
    #
    cB
    wcel
    #
    wi
    vn
    cv
    #
    cN
    cle
    wbr
    #
    vi
    cD
    @12
    @22
    @11
    @22
    cle
    wbr
    #
    @14
    @11
    cif
    #
    cif
    #
    cmpt
    #
    cB
    wcel
    #
    wi
    #
    @22
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    vi
    cD
    @12
    @30
    @11
    @30
    cle
    wbr
    #
    @14
    @11
    cif
    #
    cif
    #
    cmpt
    #
    cB
    wcel
    #
    wi
    @3
    @5
    wi
    vm
    vn
    cI
    @9
    c1
    wceq
    #
    @10
    @19
    @18
    @21
    @9
    c1
    cN
    cle
    breq1
    @37
    @17
    @20
    cB
    @37
    @17
    vi
    cD
    @12
    c1
    @11
    c1
    cle
    wbr
    #
    @14
    @11
    cif
    #
    cif
    #
    cmpt
    #
    @20
    @37
    vi
    cD
    @16
    @40
    @37
    @11
    cD
    wcel
    #
    wa
    #
    @12
    @9
    c1
    @15
    @39
    @37
    @42
    simpl
    #
    @43
    @13
    @38
    @14
    @11
    @43
    @9
    c1
    @11
    cle
    @44
    breq2d
    ifbid
    ifeq12d
    mpteq2dva
    c1
    c1
    wceq
    @41
    @20
    wceq
    c1
    eqid
    cD
    @41
    vi
    c1
    cN
    psgnfzto1st.d
    @41
    eqid
    fzto1st1
    ax-mp
    syl6eq
    eleq1d
    imbi12d
    @9
    @22
    wceq
    #
    @10
    @23
    @18
    @28
    @9
    @22
    cN
    cle
    breq1
    @45
    @17
    @27
    cB
    @45
    vi
    cD
    @16
    @26
    @45
    @42
    wa
    #
    @12
    @9
    @22
    @15
    @25
    @45
    @42
    simpl
    #
    @46
    @13
    @24
    @14
    @11
    @46
    @9
    @22
    @11
    cle
    @47
    breq2d
    ifbid
    ifeq12d
    mpteq2dva
    eleq1d
    imbi12d
    @9
    @30
    wceq
    #
    @10
    @31
    @18
    @36
    @9
    @30
    cN
    cle
    breq1
    @48
    @17
    @35
    cB
    @48
    vi
    cD
    @16
    @34
    @48
    @42
    wa
    #
    @12
    @9
    @30
    @15
    @33
    @48
    @42
    simpl
    #
    @49
    @13
    @32
    @14
    @11
    @49
    @9
    @30
    @11
    cle
    @50
    breq2d
    ifbid
    ifeq12d
    mpteq2dva
    eleq1d
    imbi12d
    @9
    cI
    wceq
    #
    @10
    @3
    @18
    @5
    @9
    cI
    cN
    cle
    breq1
    @51
    @17
    cP
    cB
    @51
    @17
    vi
    cD
    @12
    cI
    @11
    cI
    cle
    wbr
    #
    @14
    @11
    cif
    #
    cif
    #
    cmpt
    cP
    @51
    vi
    cD
    @16
    @54
    @51
    @42
    wa
    #
    @12
    @9
    cI
    @15
    @53
    @51
    @42
    simpl
    #
    @55
    @13
    @52
    @14
    @11
    @55
    @9
    cI
    @11
    cle
    @56
    breq2d
    ifbid
    ifeq12d
    mpteq2dva
    psgnfzto1st.p
    syl6eqr
    eleq1d
    imbi12d
    @21
    @1
    @19
    @20
    cG
    cbs
    cfv
    #
    cB
    cD
    cfn
    wcel
    @20
    @57
    wcel
    cD
    @7
    cfn
    psgnfzto1st.d
    c1
    cN
    fzfi
    eqeltri
    cD
    cG
    cfn
    psgnfzto1st.g
    idresperm
    ax-mp
    psgnfzto1st.b
    eleqtrri
    2a1i
    @1
    @22
    cn
    wcel
    #
    wa
    #
    @29
    wa
    #
    @31
    @36
    @60
    @31
    wa
    #
    @35
    @22
    @30
    cpr
    cD
    cpmtr
    cfv
    #
    cfv
    #
    @27
    ccom
    #
    cB
    @59
    @31
    @35
    @64
    wceq
    #
    @29
    @59
    @31
    wa
    #
    @58
    @30
    cD
    wcel
    #
    @65
    @1
    @58
    @31
    simplr
    #
    @66
    @30
    @7
    cD
    @66
    @30
    cn
    wcel
    #
    @1
    @31
    w3a
    @30
    @7
    wcel
    @66
    @69
    @1
    @31
    @66
    @22
    @68
    peano2nnd
    @1
    @58
    @31
    simpll
    #
    @59
    @31
    simpr
    #
    3jca
    cN
    @30
    elfz1b
    sylibr
    psgnfzto1st.d
    syl6eleqr
    #
    cD
    vi
    @22
    cN
    psgnfzto1st.d
    psgnfzto1stlem
    syl2anc
    adantlr
    @61
    @63
    cB
    wcel
    #
    @28
    @64
    cB
    wcel
    @61
    @62
    crn
    #
    cB
    @63
    cB
    cD
    @74
    cG
    @74
    eqid
    psgnfzto1st.g
    psgnfzto1st.b
    symgtrf
    @59
    @31
    @63
    @74
    wcel
    #
    @29
    @66
    @58
    @67
    @75
    @68
    @72
    cD
    @62
    @22
    cN
    psgnfzto1st.d
    @62
    eqid
    pmtrto1cl
    syl2anc
    adantlr
    sseldi
    @61
    @23
    @28
    @59
    @31
    @23
    @29
    @66
    @22
    @30
    cN
    @66
    @22
    @68
    nnred
    #
    @66
    @22
    c1
    @76
    @66
    1red
    readdcld
    @66
    cN
    @70
    nnred
    @66
    @22
    @76
    lep1d
    @71
    letrd
    adantlr
    @59
    @29
    @31
    simplr
    mpd
    @73
    @28
    wa
    @63
    @27
    cG
    cplusg
    cfv
    #
    co
    @64
    cB
    cD
    cB
    @77
    cG
    @63
    @27
    psgnfzto1st.g
    psgnfzto1st.b
    @77
    eqid
    #
    symgov
    cD
    cB
    @77
    cG
    @63
    @27
    psgnfzto1st.g
    psgnfzto1st.b
    @78
    symgcl
    eqeltrrd
    syl2anc
    eqeltrd
    ex
    nnindd
    imp
    sylbi
    syl
end
