include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ctan.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cneg.mm"
include "cmin.mm"
include "cdiv.mm"
include "c2.mm"
include "caddc.mm"
include "csin.mm"
include "tanval.mm"
include "2cn.mm"
include "ax-icn.mm"
include "mulcomi.mm"
include "oveq2i.mm"
include "wceq.mm"
include "sinval.mm"
include "adantr.mm"
include "simpl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efcl.mm"
include "syl.mm"
include "negicn.mm"
include "subcld.mm"
include "a1i.mm"
include "ine0.mm"
include "2ne0.mm"
include "divdiv1d.mm"
include "3eqtr4a.mm"
include "cosval.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "divcld.mm"
include "addcld.mm"
include "simpr.mm"
include "eqnetrrd.mm"
include "diveq0ad.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "divcan7d.mm"
include "3eqtrd.mm"

theorem tanval2
  let cA: class A


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( tan ` A ) = ( ( ( exp ` ( _i x. A ) ) - ( exp ` ( -u _i x. A ) ) ) / ( _i x. ( ( exp ` ( _i x. A ) ) + ( exp ` ( -u _i x. A ) ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    ctan
    cfv
    #
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    cA
    cmul
    co
    #
    ce
    cfv
    #
    cmin
    co
    #
    ci
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    @6
    @9
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cdiv
    co
    #
    @11
    @13
    cdiv
    co
    @10
    ci
    @13
    cmul
    co
    cdiv
    co
    @3
    @4
    cA
    csin
    cfv
    #
    @1
    cdiv
    co
    @15
    cA
    tanval
    @3
    @16
    @12
    @1
    @14
    cdiv
    @3
    @10
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    @10
    ci
    c2
    cmul
    co
    #
    cdiv
    co
    @16
    @12
    @17
    @19
    @10
    cdiv
    c2
    ci
    2cn
    ax-icn
    mulcomi
    oveq2i
    @0
    @16
    @18
    wceq
    @2
    cA
    sinval
    adantr
    @3
    @10
    ci
    c2
    @3
    @6
    @9
    @3
    @5
    cc
    wcel
    #
    @6
    cc
    wcel
    @3
    ci
    cc
    wcel
    #
    @0
    @20
    ax-icn
    @0
    @2
    simpl
    #
    ci
    cA
    mulcl
    sylancr
    @5
    efcl
    syl
    #
    @3
    @8
    cc
    wcel
    #
    @9
    cc
    wcel
    @3
    @7
    cc
    wcel
    @0
    @24
    negicn
    @22
    @7
    cA
    mulcl
    sylancr
    @8
    efcl
    syl
    #
    subcld
    #
    @21
    @3
    ax-icn
    a1i
    #
    c2
    cc
    wcel
    @3
    2cn
    a1i
    #
    ci
    cc0
    wne
    @3
    ine0
    a1i
    #
    c2
    cc0
    wne
    @3
    2ne0
    a1i
    #
    divdiv1d
    3eqtr4a
    @0
    @1
    @14
    wceq
    @2
    cA
    cosval
    adantr
    #
    oveq12d
    eqtrd
    @3
    @11
    @13
    c2
    @3
    @10
    ci
    @26
    @27
    @29
    divcld
    @3
    @6
    @9
    @23
    @25
    addcld
    #
    @28
    @3
    @14
    cc0
    wne
    @13
    cc0
    wne
    @3
    @1
    @14
    cc0
    @31
    @0
    @2
    simpr
    eqnetrrd
    @3
    @14
    cc0
    @13
    cc0
    @3
    @13
    c2
    @32
    @28
    @30
    diveq0ad
    necon3bid
    mpbid
    #
    @30
    divcan7d
    @3
    @10
    ci
    @13
    @26
    @27
    @32
    @29
    @33
    divdiv1d
    3eqtrd
end
