include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "csqrt.mm"
include "cfv.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "cc.mm"
include "crio.mm"
include "recn.mm"
include "adantr.mm"
include "negcld.mm"
include "sqrtval.mm"
include "syl.mm"
include "sqrtneglem.mm"
include "wreu.mm"
include "wb.mm"
include "ax-icn.mm"
include "resqrtcl.mm"
include "recnd.mm"
include "mulcl.mm"
include "sylancr.mm"
include "wrex.mm"
include "wrmo.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "neleq1.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "sqrmo.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "riota2.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem sqrtneg
  let cA: class A
  let vx: setvar x


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( sqrt ` -u A ) = ( _i x. ( sqrt ` A ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    cneg
    #
    csqrt
    cfv
    #
    vx
    cv
    #
    c2
    cexp
    co
    #
    @3
    wceq
    #
    cc0
    @5
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @5
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    vx
    cc
    crio
    #
    ci
    cA
    csqrt
    cfv
    #
    cmul
    co
    #
    @2
    @3
    cc
    wcel
    #
    @4
    @13
    wceq
    @2
    cA
    @0
    cA
    cc
    wcel
    @1
    cA
    recn
    adantr
    negcld
    #
    vx
    @3
    sqrtval
    syl
    @2
    @15
    c2
    cexp
    co
    #
    @3
    wceq
    #
    cc0
    @15
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @15
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    @13
    @15
    wceq
    #
    cA
    sqrtneglem
    #
    @2
    @15
    cc
    wcel
    #
    @12
    vx
    cc
    wreu
    #
    @24
    @25
    wb
    @2
    ci
    cc
    wcel
    @14
    cc
    wcel
    @27
    ax-icn
    @2
    @14
    cA
    resqrtcl
    recnd
    ci
    @14
    mulcl
    sylancr
    #
    @2
    @12
    vx
    cc
    wrex
    #
    @12
    vx
    cc
    wrmo
    #
    @28
    @2
    @27
    @24
    @30
    @29
    @26
    @12
    @24
    vx
    @15
    cc
    @5
    @15
    wceq
    #
    @7
    @19
    @9
    @21
    @11
    @23
    @32
    @6
    @18
    @3
    @5
    @15
    c2
    cexp
    oveq1
    eqeq1d
    @32
    @8
    @20
    cc0
    cle
    @5
    @15
    cre
    fveq2
    breq2d
    @32
    @10
    @22
    wceq
    @11
    @23
    wb
    @5
    @15
    ci
    cmul
    oveq2
    @10
    @22
    crp
    neleq1
    syl
    3anbi123d
    #
    rspcev
    syl2anc
    @2
    @16
    @31
    @17
    vx
    @3
    sqrmo
    syl
    @12
    vx
    cc
    reu5
    sylanbrc
    @12
    @24
    vx
    cc
    @15
    @33
    riota2
    syl2anc
    mpbid
    eqtrd
end
