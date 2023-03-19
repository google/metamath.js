include "wo.mm"
include "wa.mm"
include "leor.mm"
include "leid.mm"
include "ler2an.mm"
include "lear.mm"
include "lebi.mm"
include "lan.mm"

theorem vneulem1
  let wvu: term u
  let wvw: term w
  let wvx: term x
  let wvy: term y


  assert |- ( ( ( x v y ) v u ) ^ w ) = ( ( ( x v y ) v u ) ^ ( ( u v w ) ^ w ) )

  proof
    wvw
    wvu
    wvw
    wo
    #
    wvw
    wa
    #
    wvx
    wvy
    wo
    wvu
    wo
    wvw
    @1
    wvw
    @0
    wvw
    wvw
    wvu
    leor
    wvw
    leid
    ler2an
    @0
    wvw
    lear
    lebi
    lan
end
