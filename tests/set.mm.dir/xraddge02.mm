include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "xrleid.mm"
include "adantr.mm"
include "wi.mm"
include "simpl.mm"
include "0xr.mm"
include "jctir.mm"
include "xle2add.mm"
include "mpancom.mm"
include "mpand.mm"
include "wb.mm"
include "xaddid1.mm"
include "breq1d.mm"
include "sylibd.mm"

theorem xraddge02
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( 0 <_ B -> A <_ ( A +e B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cc0
    cB
    cle
    wbr
    #
    cA
    cc0
    cxad
    co
    #
    cA
    cB
    cxad
    co
    #
    cle
    wbr
    #
    cA
    @5
    cle
    wbr
    #
    @2
    cA
    cA
    cle
    wbr
    #
    @3
    @6
    @0
    @8
    @1
    cA
    xrleid
    adantr
    @0
    cc0
    cxr
    wcel
    #
    wa
    @2
    @8
    @3
    wa
    @6
    wi
    @2
    @0
    @9
    @0
    @1
    simpl
    0xr
    jctir
    cA
    cc0
    cA
    cB
    xle2add
    mpancom
    mpand
    @0
    @6
    @7
    wb
    @1
    @0
    @4
    cA
    @5
    cle
    cA
    xaddid1
    breq1d
    adantr
    sylibd
end
