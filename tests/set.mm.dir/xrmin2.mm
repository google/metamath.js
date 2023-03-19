include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wn.mm"
include "xrleid.mm"
include "iffalse.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "iftrue.mm"
include "id.mm"
include "eqbrtrd.mm"
include "pm2.61d2.mm"
include "adantl.mm"

theorem xrmin2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> if ( A <_ B , A , B ) <_ B )

  proof
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cif
    #
    cB
    cle
    wbr
    #
    cA
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
    cB
    cB
    cle
    wbr
    cB
    xrleid
    @4
    @2
    cB
    cB
    cle
    @1
    cA
    cB
    iffalse
    breq1d
    syl5ibrcom
    @1
    @2
    cA
    cB
    cle
    @1
    cA
    cB
    iftrue
    @1
    id
    eqbrtrd
    pm2.61d2
    adantl
end
