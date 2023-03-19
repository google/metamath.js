include "c3.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "c4.mm"
include "c2.mm"
include "cdc.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "3nn0.mm"
include "facp1.mm"
include "ax-mp.mm"
include "3p1e4.mm"
include "fveq2i.mm"
include "c6.mm"
include "fac3.mm"
include "oveq12i.mm"
include "6t4e24.mm"
include "eqtri.mm"
include "3eqtr3i.mm"

theorem fac4



  assert |- ( ! ` 4 ) = ; 2 4

  proof
    c3
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    c3
    cfa
    cfv
    #
    @0
    cmul
    co
    #
    c4
    cfa
    cfv
    c2
    c4
    cdc
    #
    c3
    cn0
    wcel
    @1
    @3
    wceq
    3nn0
    c3
    facp1
    ax-mp
    @0
    c4
    cfa
    3p1e4
    fveq2i
    @3
    c6
    c4
    cmul
    co
    @4
    @2
    c6
    @0
    c4
    cmul
    fac3
    3p1e4
    oveq12i
    6t4e24
    eqtri
    3eqtr3i
end
