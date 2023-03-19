include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ctan.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "catan.mm"
include "cdm.mm"
include "tancl.mm"
include "csin.mm"
include "cdiv.mm"
include "tanval.mm"
include "oveq1d.mm"
include "sincl.mm"
include "adantr.mm"
include "coscl.mm"
include "simpr.mm"
include "sqdivd.mm"
include "eqtrd.mm"
include "cmul.mm"
include "sqcld.mm"
include "negcld.mm"
include "cmin.mm"
include "caddc.mm"
include "subnegd.mm"
include "wceq.mm"
include "sincossq.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "subne0ad.mm"
include "mulm1d.mm"
include "neeqtrrd.mm"
include "neg1cn.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "biimpar.mm"
include "divmul3d.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "atandm3.mm"
include "sylanbrc.mm"

theorem atandmtan
  let cA: class A


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( tan ` A ) e. dom arctan )

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
    cc
    wcel
    @4
    c2
    cexp
    co
    #
    c1
    cneg
    #
    wne
    @4
    catan
    cdm
    wcel
    cA
    tancl
    @3
    @5
    cA
    csin
    cfv
    #
    c2
    cexp
    co
    #
    @1
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @6
    @3
    @5
    @7
    @1
    cdiv
    co
    #
    c2
    cexp
    co
    @10
    @3
    @4
    @11
    c2
    cexp
    cA
    tanval
    oveq1d
    @3
    @7
    @1
    @0
    @7
    cc
    wcel
    @2
    cA
    sincl
    adantr
    #
    @0
    @1
    cc
    wcel
    #
    @2
    cA
    coscl
    #
    adantr
    #
    @0
    @2
    simpr
    sqdivd
    eqtrd
    @3
    @10
    @6
    wne
    @8
    @6
    @9
    cmul
    co
    #
    wne
    @3
    @8
    @9
    cneg
    #
    @16
    @3
    @8
    @17
    @3
    @7
    @12
    sqcld
    #
    @3
    @9
    @3
    @1
    @15
    sqcld
    #
    negcld
    @3
    @8
    @17
    cmin
    co
    #
    c1
    cc0
    @3
    @20
    @8
    @9
    caddc
    co
    #
    c1
    @3
    @8
    @9
    @18
    @19
    subnegd
    @0
    @21
    c1
    wceq
    @2
    cA
    sincossq
    adantr
    eqtrd
    c1
    cc0
    wne
    @3
    ax-1ne0
    a1i
    eqnetrd
    subne0ad
    @3
    @9
    @19
    mulm1d
    neeqtrrd
    @3
    @10
    @6
    @8
    @16
    @3
    @8
    @6
    @9
    @18
    @6
    cc
    wcel
    @3
    neg1cn
    a1i
    @19
    @0
    @9
    cc0
    wne
    #
    @2
    @0
    @13
    @22
    @2
    wb
    @14
    @1
    sqne0
    syl
    biimpar
    divmul3d
    necon3bid
    mpbird
    eqnetrd
    @4
    atandm3
    sylanbrc
end
