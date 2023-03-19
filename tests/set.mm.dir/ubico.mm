include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "ltnrd.mm"
include "pm2.65i.mm"
include "elico2.mm"
include "mtbiri.mm"

theorem ubico
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR* ) -> -. B e. ( A [,) B ) )

  proof
    cA
    cr
    wcel
    cB
    cxr
    wcel
    wa
    cB
    cA
    cB
    cico
    co
    wcel
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cB
    clt
    wbr
    #
    w3a
    #
    @3
    @2
    @0
    @1
    @2
    simp3
    @3
    cB
    @0
    @1
    @2
    simp1
    ltnrd
    pm2.65i
    cA
    cB
    cB
    elico2
    mtbiri
end
