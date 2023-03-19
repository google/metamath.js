include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "2z.mm"
include "dvdsmul1.mm"
include "mpan.mm"
include "adantr.mm"
include "wb.mm"
include "breq2.mm"
include "adantl.mm"
include "mpbird.mm"

theorem 2teven
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B = ( 2 x. A ) ) -> 2 || B )

  proof
    cA
    cz
    wcel
    #
    cB
    c2
    cA
    cmul
    co
    #
    wceq
    #
    wa
    c2
    cB
    cdvds
    wbr
    #
    c2
    @1
    cdvds
    wbr
    #
    @0
    @4
    @2
    c2
    cz
    wcel
    @0
    @4
    2z
    c2
    cA
    dvdsmul1
    mpan
    adantr
    @2
    @3
    @4
    wb
    @0
    cB
    @1
    c2
    cdvds
    breq2
    adantl
    mpbird
end
