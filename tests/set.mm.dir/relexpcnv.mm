include "cn0.mm"
include "wcel.mm"
include "crelexp.mm"
include "co.mm"
include "ccnv.mm"
include "wceq.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "cnveqd.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "relexp1g.mm"
include "cvv.mm"
include "cnvexg.mm"
include "syl.mm"
include "eqtr4d.mm"
include "w3a.mm"
include "ccom.mm"
include "cnvco.mm"
include "simp3.mm"
include "coeq2d.mm"
include "syl5eq.mm"
include "simp2.mm"
include "simp1.mm"
include "relexpsucnnr.mm"
include "syl2anc.mm"
include "relexpsucnnl.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "wa.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cnvresid.mm"
include "uncom.mm"
include "df-rn.mm"
include "dfdm4.mm"
include "uneq12i.mm"
include "eqtri.mm"
include "reseq2i.mm"
include "relexp0g.mm"
include "sylan9eq.mm"
include "adantr.mm"
include "simpr.mm"
include "3syl.mm"
include "eqtrd.mm"
include "3eqtr4a.mm"
include "ex.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp.mm"

theorem relexpcnv
  let cR: class R
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vm: setvar m


  assert |- ( ( N e. NN0 /\ R e. V ) -> `' ( R ^r N ) = ( `' R ^r N ) )

  proof
    cN
    cn0
    wcel
    #
    cR
    cV
    wcel
    #
    cR
    cN
    crelexp
    co
    #
    ccnv
    #
    cR
    ccnv
    #
    cN
    crelexp
    co
    #
    wceq
    #
    @0
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @1
    @6
    wi
    #
    cN
    elnn0
    @7
    @9
    @8
    @1
    cR
    vn
    cv
    #
    crelexp
    co
    #
    ccnv
    #
    @4
    @10
    crelexp
    co
    #
    wceq
    #
    wi
    @1
    cR
    c1
    crelexp
    co
    #
    ccnv
    #
    @4
    c1
    crelexp
    co
    #
    wceq
    #
    wi
    @1
    cR
    vm
    cv
    #
    crelexp
    co
    #
    ccnv
    #
    @4
    @19
    crelexp
    co
    #
    wceq
    #
    wi
    @1
    cR
    @19
    c1
    caddc
    co
    #
    crelexp
    co
    #
    ccnv
    #
    @4
    @24
    crelexp
    co
    #
    wceq
    #
    wi
    @9
    vn
    vm
    cN
    @10
    c1
    wceq
    #
    @14
    @18
    @1
    @29
    @12
    @16
    @13
    @17
    @29
    @11
    @15
    @10
    c1
    cR
    crelexp
    oveq2
    cnveqd
    @10
    c1
    @4
    crelexp
    oveq2
    eqeq12d
    imbi2d
    vn
    vm
    weq
    #
    @14
    @23
    @1
    @30
    @12
    @21
    @13
    @22
    @30
    @11
    @20
    @10
    @19
    cR
    crelexp
    oveq2
    cnveqd
    @10
    @19
    @4
    crelexp
    oveq2
    eqeq12d
    imbi2d
    @10
    @24
    wceq
    #
    @14
    @28
    @1
    @31
    @12
    @26
    @13
    @27
    @31
    @11
    @25
    @10
    @24
    cR
    crelexp
    oveq2
    cnveqd
    @10
    @24
    @4
    crelexp
    oveq2
    eqeq12d
    imbi2d
    @10
    cN
    wceq
    #
    @14
    @6
    @1
    @32
    @12
    @3
    @13
    @5
    @32
    @11
    @2
    @10
    cN
    cR
    crelexp
    oveq2
    cnveqd
    @10
    cN
    @4
    crelexp
    oveq2
    eqeq12d
    imbi2d
    @1
    @16
    @4
    @17
    @1
    @15
    cR
    cR
    cV
    relexp1g
    cnveqd
    @1
    @4
    cvv
    wcel
    #
    @17
    @4
    wceq
    cR
    cV
    cnvexg
    #
    @4
    cvv
    relexp1g
    syl
    eqtr4d
    @19
    cn
    wcel
    #
    @1
    @23
    @28
    @35
    @1
    @23
    @28
    @35
    @1
    @23
    w3a
    #
    @20
    cR
    ccom
    #
    ccnv
    #
    @4
    @22
    ccom
    #
    @26
    @27
    @36
    @38
    @4
    @21
    ccom
    @39
    @20
    cR
    cnvco
    @36
    @21
    @22
    @4
    @35
    @1
    @23
    simp3
    coeq2d
    syl5eq
    @36
    @25
    @37
    @36
    @1
    @35
    @25
    @37
    wceq
    @35
    @1
    @23
    simp2
    #
    @35
    @1
    @23
    simp1
    #
    cR
    @19
    cV
    relexpsucnnr
    syl2anc
    cnveqd
    @36
    @33
    @35
    @27
    @39
    wceq
    @36
    @1
    @33
    @40
    @34
    syl
    @41
    @4
    @19
    cvv
    relexpsucnnl
    syl2anc
    3eqtr4d
    3exp
    a2d
    nnind
    @8
    @1
    @6
    @8
    @1
    wa
    #
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cres
    #
    ccnv
    #
    cid
    @4
    cdm
    #
    @4
    crn
    #
    cun
    #
    cres
    #
    @3
    @5
    @47
    @46
    @51
    @45
    cnvresid
    @45
    @50
    cid
    @45
    @44
    @43
    cun
    @50
    @43
    @44
    uncom
    @44
    @48
    @43
    @49
    cR
    df-rn
    cR
    dfdm4
    uneq12i
    eqtri
    reseq2i
    eqtri
    @42
    @2
    @46
    @8
    @1
    @2
    cR
    cc0
    crelexp
    co
    @46
    cN
    cc0
    cR
    crelexp
    oveq2
    cR
    cV
    relexp0g
    sylan9eq
    cnveqd
    @42
    @5
    @4
    cc0
    crelexp
    co
    #
    @51
    @8
    @5
    @52
    wceq
    @1
    cN
    cc0
    @4
    crelexp
    oveq2
    adantr
    @42
    @1
    @33
    @52
    @51
    wceq
    @8
    @1
    simpr
    @34
    @4
    cvv
    relexp0g
    3syl
    eqtrd
    3eqtr4a
    ex
    jaoi
    sylbi
    imp
end
