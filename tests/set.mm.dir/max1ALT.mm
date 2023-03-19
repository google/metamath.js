include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wn.mm"
include "leid.mm"
include "iffalse.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "id.mm"
include "iftrue.mm"
include "breqtrrd.mm"
include "pm2.61d2.mm"

theorem max1ALT
  let cA: class A
  let cB: class B


  assert |- ( A e. RR -> A <_ if ( A <_ B , B , A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cA
    @1
    cB
    cA
    cif
    #
    cle
    wbr
    #
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
    leid
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
end
