include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "ax-hvcom.mm"
include "mpan2.mm"
include "ax-hvaddid.mm"
include "eqtr3d.mm"

theorem hvaddid2
  let cA: class A


  assert |- ( A e. ~H -> ( 0h +h A ) = A )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    cva
    co
    #
    c0v
    cA
    cva
    co
    #
    cA
    @0
    c0v
    chil
    wcel
    @1
    @2
    wceq
    ax-hv0cl
    cA
    c0v
    ax-hvcom
    mpan2
    cA
    ax-hvaddid
    eqtr3d
end
