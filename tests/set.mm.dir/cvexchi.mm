include "cin.mm"
include "ccv.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "cvexchlem.mm"
include "cort.mm"
include "cfv.mm"
include "choccli.mm"
include "chdmj1i.mm"
include "incom.mm"
include "eqtri.mm"
include "breq1i.mm"
include "chdmm1i.mm"
include "chjcomi.mm"
include "breq2i.mm"
include "3imtr4i.mm"
include "cch.mm"
include "wcel.mm"
include "wb.mm"
include "chjcli.mm"
include "cvcon3.mm"
include "mp2an.mm"
include "chincli.mm"
include "impbii.mm"

theorem cvexchi
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume chpssat.1: |- A e. CH
  assume chpssat.2: |- B e. CH


  assert |- ( ( A i^i B ) <oH B <-> A <oH ( A vH B ) )

  proof
    cA
    cB
    cin
    #
    cB
    ccv
    wbr
    #
    cA
    cA
    cB
    chj
    co
    #
    ccv
    wbr
    #
    cA
    cB
    chpssat.1
    chpssat.2
    cvexchlem
    @2
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    ccv
    wbr
    #
    cB
    cort
    cfv
    #
    @0
    cort
    cfv
    #
    ccv
    wbr
    #
    @3
    @1
    @7
    @5
    cin
    #
    @5
    ccv
    wbr
    @7
    @7
    @5
    chj
    co
    #
    ccv
    wbr
    @6
    @9
    @7
    @5
    cB
    chpssat.2
    choccli
    #
    cA
    chpssat.1
    choccli
    #
    cvexchlem
    @4
    @10
    @5
    ccv
    @4
    @5
    @7
    cin
    @10
    cA
    cB
    chpssat.1
    chpssat.2
    chdmj1i
    @5
    @7
    incom
    eqtri
    breq1i
    @8
    @11
    @7
    ccv
    @8
    @5
    @7
    chj
    co
    @11
    cA
    cB
    chpssat.1
    chpssat.2
    chdmm1i
    @5
    @7
    @13
    @12
    chjcomi
    eqtri
    breq2i
    3imtr4i
    cA
    cch
    wcel
    @2
    cch
    wcel
    @3
    @6
    wb
    chpssat.1
    cA
    cB
    chpssat.1
    chpssat.2
    chjcli
    cA
    @2
    cvcon3
    mp2an
    @0
    cch
    wcel
    cB
    cch
    wcel
    @1
    @9
    wb
    cA
    cB
    chpssat.1
    chpssat.2
    chincli
    chpssat.2
    @0
    cB
    cvcon3
    mp2an
    3imtr4i
    impbii
end
