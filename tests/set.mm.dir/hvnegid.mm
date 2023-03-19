include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "c0v.mm"
include "wceq.mm"
include "hvsubval.mm"
include "anidms.mm"
include "hvsubid.mm"
include "eqtr3d.mm"

theorem hvnegid
  let cA: class A


  assert |- ( A e. ~H -> ( A +h ( -u 1 .h A ) ) = 0h )

  proof
    cA
    chil
    wcel
    #
    cA
    cA
    cmv
    co
    #
    cA
    c1
    cneg
    cA
    csm
    co
    cva
    co
    #
    c0v
    @0
    @1
    @2
    wceq
    cA
    cA
    hvsubval
    anidms
    cA
    hvsubid
    eqtr3d
end
