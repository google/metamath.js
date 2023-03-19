include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cupgr.mm"
include "wcel.mm"
include "cwwlksn.mm"
include "co.mm"
include "cn0.mm"
include "wi.mm"
include "wlkcl.mm"
include "adantr.mm"
include "cwwlks.mm"
include "c1.mm"
include "caddc.mm"
include "wlkiswwlks1.mm"
include "com12.mm"
include "ad2antrl.mm"
include "imp.mm"
include "wlklenvp1.mm"
include "oveq1.mm"
include "adantl.mm"
include "eqtrd.mm"
include "wb.mm"
include "eleq1.mm"
include "iswwlksn.mm"
include "syl6bi.mm"
include "impcom.mm"
include "mpbir2and.mm"
include "ex.mm"
include "mpancom.mm"

theorem wlklnwwlkln1
  let cP: class P
  let cF: class F
  let cG: class G
  let cN: class N


  assert |- ( G e. UPGraph -> ( ( F ( Walks ` G ) P /\ ( # ` F ) = N ) -> P e. ( N WWalksN G ) ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    cG
    cupgr
    wcel
    #
    cP
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @1
    cn0
    wcel
    #
    @3
    @4
    @5
    wi
    @0
    @6
    @2
    cP
    cF
    cG
    wlkcl
    adantr
    @6
    @3
    wa
    #
    @4
    @5
    @7
    @4
    wa
    @5
    cP
    cG
    cwwlks
    cfv
    wcel
    #
    cP
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    @7
    @4
    @8
    @0
    @4
    @8
    wi
    @6
    @2
    @4
    @0
    @8
    cP
    cF
    cG
    wlkiswwlks1
    com12
    ad2antrl
    imp
    @7
    @11
    @4
    @7
    @9
    @1
    c1
    caddc
    co
    #
    @10
    @0
    @9
    @12
    wceq
    @6
    @2
    cP
    cF
    cG
    wlklenvp1
    ad2antrl
    @3
    @12
    @10
    wceq
    #
    @6
    @2
    @13
    @0
    @1
    cN
    c1
    caddc
    oveq1
    adantl
    adantl
    eqtrd
    adantr
    @7
    @5
    @8
    @11
    wa
    wb
    #
    @4
    @3
    @6
    @14
    @2
    @6
    @14
    wi
    @0
    @2
    @6
    cN
    cn0
    wcel
    @14
    @1
    cN
    cn0
    eleq1
    cG
    cN
    cP
    iswwlksn
    syl6bi
    adantl
    impcom
    adantr
    mpbir2and
    ex
    mpancom
    com12
end
