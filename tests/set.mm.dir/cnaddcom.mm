include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "cop.mm"
include "cplusg.mm"
include "caddc.mm"
include "cpr.mm"
include "cabl.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "cnaddabl.mm"
include "cvv.mm"
include "cnex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "addex.mm"
include "grpplusg.mm"
include "ablcom.mm"
include "mp3an1.mm"

theorem cnaddcom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + B ) = ( B + A ) )

  proof
    cnx
    cbs
    cfv
    cc
    cop
    cnx
    cplusg
    cfv
    caddc
    cop
    cpr
    #
    cabl
    wcel
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cB
    cA
    caddc
    co
    wceq
    @0
    @0
    eqid
    #
    cnaddabl
    cc
    caddc
    @0
    cA
    cB
    cc
    cvv
    wcel
    cc
    @0
    cbs
    cfv
    wceq
    cnex
    cc
    caddc
    @0
    cvv
    @1
    grpbase
    ax-mp
    caddc
    cvv
    wcel
    caddc
    @0
    cplusg
    cfv
    wceq
    addex
    cc
    caddc
    @0
    cvv
    @1
    grpplusg
    ax-mp
    ablcom
    mp3an1
end
