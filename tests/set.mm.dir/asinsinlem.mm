include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wa.mm"
include "cc0.mm"
include "ci.mm"
include "cmul.mm"
include "ce.mm"
include "ccos.mm"
include "clt.mm"
include "ax-icn.mm"
include "simpl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "recld.mm"
include "reefcld.mm"
include "cr.mm"
include "wbr.mm"
include "w3a.mm"
include "simpr.mm"
include "cxr.mm"
include "wb.mm"
include "neghalfpirx.mm"
include "halfpire.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "sylib.mm"
include "simp1d.mm"
include "recoscld.mm"
include "efgt0.mm"
include "syl.mm"
include "cosq14gt0.mm"
include "adantl.mm"
include "mulgt0d.mm"
include "cim.mm"
include "csin.mm"
include "caddc.mm"
include "wceq.mm"
include "efeul.mm"
include "fveq2d.mm"
include "imcld.mm"
include "recnd.mm"
include "resincld.mm"
include "addcld.mm"
include "remul2d.mm"
include "crred.mm"
include "imre.mm"
include "c1.mm"
include "mulneg1i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "negicn.mm"
include "a1i.mm"
include "mulassd.mm"
include "mulid2.mm"
include "adantr.mm"
include "3eqtr3a.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "breqtrrd.mm"

theorem asinsinlem
  let cA: class A


  assert |- ( ( A e. CC /\ ( Re ` A ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) ) -> 0 < ( Re ` ( exp ` ( _i x. A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @2
    cioo
    co
    wcel
    #
    wa
    #
    cc0
    ci
    cA
    cmul
    co
    #
    cre
    cfv
    #
    ce
    cfv
    #
    @1
    ccos
    cfv
    #
    cmul
    co
    #
    @6
    ce
    cfv
    #
    cre
    cfv
    #
    clt
    @5
    @8
    @9
    @5
    @7
    @5
    @6
    @5
    ci
    cc
    wcel
    #
    @0
    @6
    cc
    wcel
    #
    ax-icn
    @0
    @4
    simpl
    #
    ci
    cA
    mulcl
    sylancr
    #
    recld
    #
    reefcld
    #
    @5
    @1
    @5
    @1
    cr
    wcel
    #
    @3
    @1
    clt
    wbr
    #
    @1
    @2
    clt
    wbr
    #
    @5
    @4
    @19
    @20
    @21
    w3a
    #
    @0
    @4
    simpr
    @3
    cxr
    wcel
    @2
    cxr
    wcel
    @4
    @22
    wb
    neghalfpirx
    @2
    halfpire
    rexri
    @3
    @2
    @1
    elioo2
    mp2an
    sylib
    simp1d
    recoscld
    @5
    @7
    cr
    wcel
    cc0
    @8
    clt
    wbr
    @17
    @7
    efgt0
    syl
    @4
    cc0
    @9
    clt
    wbr
    @0
    @1
    cosq14gt0
    adantl
    mulgt0d
    @5
    @12
    @8
    @6
    cim
    cfv
    #
    ccos
    cfv
    #
    ci
    @23
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    cre
    cfv
    @8
    @27
    cre
    cfv
    #
    cmul
    co
    @10
    @5
    @11
    @28
    cre
    @5
    @14
    @11
    @28
    wceq
    @16
    @6
    efeul
    syl
    fveq2d
    @5
    @8
    @27
    @18
    @5
    @24
    @26
    @5
    @24
    @5
    @23
    @5
    @6
    @16
    imcld
    #
    recoscld
    #
    recnd
    @5
    @13
    @25
    cc
    wcel
    @26
    cc
    wcel
    ax-icn
    @5
    @25
    @5
    @23
    @30
    resincld
    #
    recnd
    ci
    @25
    mulcl
    sylancr
    addcld
    remul2d
    @5
    @29
    @9
    @8
    cmul
    @5
    @29
    @24
    @9
    @5
    @24
    @25
    @31
    @32
    crred
    @5
    @23
    @1
    ccos
    @5
    @23
    ci
    cneg
    #
    @6
    cmul
    co
    #
    cre
    cfv
    #
    @1
    @5
    @14
    @23
    @35
    wceq
    @16
    @6
    imre
    syl
    @5
    @34
    cA
    cre
    @5
    @33
    ci
    cmul
    co
    #
    cA
    cmul
    co
    c1
    cA
    cmul
    co
    #
    @34
    cA
    @36
    c1
    cA
    cmul
    @36
    ci
    ci
    cmul
    co
    #
    cneg
    c1
    cneg
    #
    cneg
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg1i
    @38
    @39
    ixi
    negeqi
    negneg1e1
    3eqtri
    oveq1i
    @5
    @33
    ci
    cA
    @33
    cc
    wcel
    @5
    negicn
    a1i
    @13
    @5
    ax-icn
    a1i
    @15
    mulassd
    @0
    @37
    cA
    wceq
    @4
    cA
    mulid2
    adantr
    3eqtr3a
    fveq2d
    eqtrd
    fveq2d
    eqtrd
    oveq2d
    3eqtrd
    breqtrrd
end
