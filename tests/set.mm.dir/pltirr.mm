include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "eqid.mm"
include "wne.mm"
include "wi.mm"
include "pltne.mm"
include "3anidm23.mm"
include "necon2bd.mm"
include "mpi.mm"

theorem pltirr
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let cX: class X
  assume pltne.s: |- .< = ( lt ` K )


  assert |- ( ( K e. A /\ X e. B ) -> -. X .< X )

  proof
    cK
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cX
    wceq
    cX
    cX
    c.lt
    wbr
    #
    wn
    cX
    eqid
    @2
    @3
    cX
    cX
    @0
    @1
    @3
    cX
    cX
    wne
    wi
    cA
    cB
    cB
    c.lt
    cK
    cX
    cX
    pltne.s
    pltne
    3anidm23
    necon2bd
    mpi
end
