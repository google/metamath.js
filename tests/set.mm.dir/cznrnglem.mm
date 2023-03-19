include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cmulr.mm"
include "cmpt2.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "baseid.mm"
include "basendxnmulrndx.mm"
include "setsnid.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "3eqtri.mm"

theorem cznrnglem
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume cznrng.y: |- Y = ( Z/nZ ` N )
  assume cznrng.b: |- B = ( Base ` Y )
  assume cznrng.x: |- X = ( Y sSet <. ( .r ` ndx ) , ( x e. B , y e. B |-> C ) >. )


  assert |- B = ( Base ` X )

  proof
    cB
    cY
    cbs
    cfv
    cY
    cnx
    cmulr
    cfv
    #
    vx
    vy
    cB
    cB
    cC
    cmpt2
    #
    cop
    csts
    co
    #
    cbs
    cfv
    cX
    cbs
    cfv
    cznrng.b
    @1
    @0
    cbs
    cY
    baseid
    basendxnmulrndx
    setsnid
    @2
    cX
    cbs
    cX
    @2
    cznrng.x
    eqcomi
    fveq2i
    3eqtri
end
