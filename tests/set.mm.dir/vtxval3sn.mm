include "csn.mm"
include "cop.mm"
include "opid.mm"
include "eqcomi.mm"
include "sneqi.mm"
include "vtxvalsnop.mm"

theorem vtxval3sn
  let cA: class A
  assume vtxval3sn.a: |- A e. _V


  assert |- ( Vtx ` { { { A } } } ) = { A }

  proof
    cA
    cA
    csn
    csn
    #
    csn
    vtxval3sn.a
    @0
    cA
    cA
    cop
    #
    @1
    @0
    cA
    vtxval3sn.a
    opid
    eqcomi
    sneqi
    vtxvalsnop
end
