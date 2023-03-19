include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wn.mm"
include "xrleid.mm"
include "iffalse.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "id.mm"
include "iftrue.mm"
include "breqtrrd.mm"
include "pm2.61d2.mm"
include "adantr.mm"

theorem xrmax1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> A <_ if ( A <_ B , B , A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cif
    #
    cle
    wbr
    #
    cB
    cxr
    wcel
    @0
    @1
    @3
    @0
    @3
    @1
    wn
    #
    cA
    cA
    cle
    wbr
    cA
    xrleid
    @4
    @2
    cA
    cA
    cle
    @1
    cB
    cA
    iffalse
    breq2d
    syl5ibrcom
    @1
    cA
    cB
    @2
    cle
    @1
    id
    @1
    cB
    cA
    iftrue
    breqtrrd
    pm2.61d2
    adantr
end
