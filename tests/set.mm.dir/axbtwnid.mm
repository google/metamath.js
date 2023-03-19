include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "cc0.mm"
include "cicc.mm"
include "wrex.mm"
include "wb.mm"
include "simp2.mm"
include "simp3.mm"
include "brbtwn.mm"
include "syl3anc.mm"
include "cc.mm"
include "wi.mm"
include "cr.mm"
include "cle.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "recnd.mm"
include "wa.mm"
include "eqeefv.mm"
include "3adant1.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "mpan.mm"
include "ad2antlr.mm"
include "oveq1d.mm"
include "subcl.mm"
include "simplr.mm"
include "simpll3.mm"
include "fveecn.mm"
include "sylancom.mm"
include "adddird.mm"
include "mulid2d.mm"
include "3eqtr3rd.mm"
include "eqeq2d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "biimprd.mm"
include "sylan2.mm"
include "rexlimdva.mm"
include "sylbid.mm"

theorem axbtwnid
  let cA: class A
  let cB: class B
  let cN: class N
  let vt: setvar t
  let vi: setvar i


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> ( A Btwn <. B , B >. -> A = B ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cB
    cB
    cop
    cbtwn
    wbr
    #
    vi
    cv
    #
    cA
    cfv
    #
    c1
    vt
    cv
    #
    cmin
    co
    #
    @6
    cB
    cfv
    #
    cmul
    co
    @8
    @10
    cmul
    co
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    vt
    cc0
    c1
    cicc
    co
    #
    wrex
    #
    cA
    cB
    wceq
    #
    @4
    @2
    @3
    @3
    @5
    @16
    wb
    @0
    @2
    @3
    simp2
    @0
    @2
    @3
    simp3
    #
    @18
    vt
    cA
    cB
    cB
    vi
    cN
    brbtwn
    syl3anc
    @4
    @14
    @17
    vt
    @15
    @8
    @15
    wcel
    #
    @4
    @8
    cc
    wcel
    #
    @14
    @17
    wi
    @19
    @8
    @19
    @8
    cr
    wcel
    cc0
    @8
    cle
    wbr
    @8
    c1
    cle
    wbr
    cc0
    c1
    @8
    0re
    1re
    elicc2i
    simp1bi
    recnd
    @4
    @20
    wa
    #
    @17
    @14
    @21
    @17
    @7
    @10
    wceq
    #
    vi
    @13
    wral
    #
    @14
    @4
    @17
    @23
    wb
    #
    @20
    @2
    @3
    @24
    @0
    cA
    cB
    vi
    cN
    eqeefv
    3adant1
    adantr
    @21
    @22
    @12
    vi
    @13
    @21
    @6
    @13
    wcel
    #
    wa
    #
    @10
    @11
    @7
    @26
    @9
    @8
    caddc
    co
    #
    @10
    cmul
    co
    c1
    @10
    cmul
    co
    @11
    @10
    @26
    @27
    c1
    @10
    cmul
    @20
    @27
    c1
    wceq
    #
    @4
    @25
    c1
    cc
    wcel
    #
    @20
    @28
    ax-1cn
    c1
    @8
    npcan
    mpan
    ad2antlr
    oveq1d
    @26
    @9
    @8
    @10
    @20
    @9
    cc
    wcel
    #
    @4
    @25
    @29
    @20
    @30
    ax-1cn
    c1
    @8
    subcl
    mpan
    ad2antlr
    @4
    @20
    @25
    simplr
    @21
    @25
    @3
    @10
    cc
    wcel
    @0
    @2
    @3
    @20
    @25
    simpll3
    cB
    @6
    cN
    fveecn
    sylancom
    #
    adddird
    @26
    @10
    @31
    mulid2d
    3eqtr3rd
    eqeq2d
    ralbidva
    bitrd
    biimprd
    sylan2
    rexlimdva
    sylbid
end
