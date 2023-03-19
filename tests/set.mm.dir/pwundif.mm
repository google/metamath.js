include "cun.mm"
include "cpw.mm"
include "cdif.mm"
include "undif1.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "pwunss.mm"
include "unss.mm"
include "mpbir.mm"
include "simpli.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "eqtr2i.mm"

theorem pwundif
  let cA: class A
  let cB: class B


  assert |- ~P ( A u. B ) = ( ( ~P ( A u. B ) \ ~P A ) u. ~P A )

  proof
    cA
    cB
    cun
    cpw
    #
    cA
    cpw
    #
    cdif
    @1
    cun
    @0
    @1
    cun
    #
    @0
    @0
    @1
    undif1
    @1
    @0
    wss
    #
    @2
    @0
    wceq
    @3
    cB
    cpw
    #
    @0
    wss
    #
    @3
    @5
    wa
    @1
    @4
    cun
    @0
    wss
    cA
    cB
    pwunss
    @1
    @4
    @0
    unss
    mpbir
    simpli
    @1
    @0
    ssequn2
    mpbi
    eqtr2i
end
