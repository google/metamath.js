include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "rpre.mm"
include "leidd.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "modabs.mm"
include "ex.mm"
include "3anidm23.mm"
include "mpd.mm"

theorem modabs2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A mod B ) mod B ) = ( A mod B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    cB
    cB
    cle
    wbr
    #
    cA
    cB
    cmo
    co
    #
    cB
    cmo
    co
    @3
    wceq
    #
    @1
    @2
    @0
    @1
    cB
    cB
    rpre
    leidd
    adantl
    @0
    @1
    @2
    @4
    wi
    @0
    @1
    @1
    w3a
    @2
    @4
    cA
    cB
    cB
    modabs
    ex
    3anidm23
    mpd
end
