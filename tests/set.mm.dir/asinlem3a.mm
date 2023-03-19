include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "csqrt.mm"
include "cre.mm"
include "caddc.mm"
include "ci.mm"
include "cmul.mm"
include "cr.mm"
include "imcl.mm"
include "adantr.mm"
include "renegcld.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "recld.mm"
include "le0neg1d.mm"
include "biimpa.mm"
include "sqrtrege0d.mm"
include "addge0d.mm"
include "ax-icn.mm"
include "simpl.mm"
include "mulcl.mm"
include "readdd.mm"
include "negicn.mm"
include "renegd.mm"
include "negnegi.mm"
include "oveq1i.mm"
include "wceq.mm"
include "mulneg1.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "imre.mm"
include "negeqd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"

theorem asinlem3a
  let cA: class A


  assert |- ( ( A e. CC /\ ( Im ` A ) <_ 0 ) -> 0 <_ ( Re ` ( ( _i x. A ) + ( sqrt ` ( 1 - ( A ^ 2 ) ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cim
    cfv
    #
    cc0
    cle
    wbr
    #
    wa
    #
    cc0
    @1
    cneg
    #
    c1
    cA
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    cre
    cfv
    #
    caddc
    co
    #
    ci
    cA
    cmul
    co
    #
    @7
    caddc
    co
    cre
    cfv
    #
    cle
    @3
    @4
    @8
    @3
    @1
    @0
    @1
    cr
    wcel
    @2
    cA
    imcl
    #
    adantr
    renegcld
    @3
    @7
    @3
    @6
    @3
    c1
    cc
    wcel
    @5
    cc
    wcel
    #
    @6
    cc
    wcel
    ax-1cn
    @0
    @13
    @2
    cA
    sqcl
    adantr
    c1
    @5
    subcl
    sylancr
    #
    sqrtcld
    #
    recld
    @0
    @2
    cc0
    @4
    cle
    wbr
    @0
    @1
    @12
    le0neg1d
    biimpa
    @3
    @6
    @14
    sqrtrege0d
    addge0d
    @3
    @11
    @10
    cre
    cfv
    #
    @8
    caddc
    co
    @9
    @3
    @10
    @7
    @3
    ci
    cc
    wcel
    @0
    @10
    cc
    wcel
    ax-icn
    @0
    @2
    simpl
    #
    ci
    cA
    mulcl
    sylancr
    @15
    readdd
    @3
    @16
    @4
    @8
    caddc
    @3
    ci
    cneg
    #
    cA
    cmul
    co
    #
    cneg
    #
    cre
    cfv
    @19
    cre
    cfv
    #
    cneg
    @16
    @4
    @3
    @19
    @3
    @18
    cc
    wcel
    #
    @0
    @19
    cc
    wcel
    negicn
    @17
    @18
    cA
    mulcl
    sylancr
    renegd
    @3
    @10
    @20
    cre
    @3
    @10
    @18
    cneg
    #
    cA
    cmul
    co
    #
    @20
    @23
    ci
    cA
    cmul
    ci
    ax-icn
    negnegi
    oveq1i
    @3
    @22
    @0
    @24
    @20
    wceq
    negicn
    @17
    @18
    cA
    mulneg1
    sylancr
    syl5eqr
    fveq2d
    @3
    @1
    @21
    @0
    @1
    @21
    wceq
    @2
    cA
    imre
    adantr
    negeqd
    3eqtr4d
    oveq1d
    eqtrd
    breqtrrd
end
