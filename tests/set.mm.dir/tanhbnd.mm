include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ctan.mm"
include "cfv.mm"
include "cdiv.mm"
include "c1.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "cioo.mm"
include "retanhcl.mm"
include "cc.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ccos.mm"
include "rpcoshcl.mm"
include "rpne0d.mm"
include "tancld.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "ine0.mm"
include "divnegd.mm"
include "wceq.mm"
include "mulneg2.mm"
include "fveq2d.mm"
include "tanneg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "renegcl.mm"
include "tanhlt1.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "1re.mm"
include "ltnegcon1.mm"
include "sylancl.mm"
include "mpbid.mm"
include "cxr.mm"
include "w3a.mm"
include "neg1rr.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"

theorem tanhbnd
  let cA: class A


  assert |- ( A e. RR -> ( ( tan ` ( _i x. A ) ) / _i ) e. ( -u 1 (,) 1 ) )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    #
    ctan
    cfv
    #
    ci
    cdiv
    co
    #
    cr
    wcel
    #
    c1
    cneg
    #
    @3
    clt
    wbr
    #
    @3
    c1
    clt
    wbr
    #
    @3
    @5
    c1
    cioo
    co
    wcel
    #
    cA
    retanhcl
    #
    @0
    @3
    cneg
    #
    c1
    clt
    wbr
    #
    @6
    @0
    @10
    ci
    cA
    cneg
    #
    cmul
    co
    #
    ctan
    cfv
    #
    ci
    cdiv
    co
    #
    c1
    clt
    @0
    @10
    @2
    cneg
    #
    ci
    cdiv
    co
    @15
    @0
    @2
    ci
    @0
    @1
    @0
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    ax-icn
    cA
    recn
    #
    ci
    cA
    mulcl
    sylancr
    #
    @0
    @1
    ccos
    cfv
    #
    cA
    rpcoshcl
    rpne0d
    #
    tancld
    @17
    @0
    ax-icn
    a1i
    ci
    cc0
    wne
    @0
    ine0
    a1i
    divnegd
    @0
    @14
    @16
    ci
    cdiv
    @0
    @14
    @1
    cneg
    #
    ctan
    cfv
    #
    @16
    @0
    @13
    @24
    ctan
    @0
    @17
    @18
    @13
    @24
    wceq
    ax-icn
    @20
    ci
    cA
    mulneg2
    sylancr
    fveq2d
    @0
    @19
    @22
    cc0
    wne
    @25
    @16
    wceq
    @21
    @23
    @1
    tanneg
    syl2anc
    eqtrd
    oveq1d
    eqtr4d
    @0
    @12
    cr
    wcel
    @15
    c1
    clt
    wbr
    cA
    renegcl
    @12
    tanhlt1
    syl
    eqbrtrd
    @0
    @4
    c1
    cr
    wcel
    @11
    @6
    wb
    @9
    1re
    @3
    c1
    ltnegcon1
    sylancl
    mpbid
    cA
    tanhlt1
    @5
    cxr
    wcel
    c1
    cxr
    wcel
    @8
    @4
    @6
    @7
    w3a
    wb
    @5
    neg1rr
    rexri
    c1
    1re
    rexri
    @5
    c1
    @3
    elioo2
    mp2an
    syl3anbrc
end
