include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "matbas.mm"
include "cv.mm"
include "cplusg.mm"
include "matplusg.mm"
include "oveqdr.mm"
include "grpinvpropd.mm"

theorem matinvg
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume matbas.a: |- A = ( N Mat R )
  assume matbas.g: |- G = ( R freeLMod ( N X. N ) )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( invg ` G ) = ( invg ` A ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    wa
    #
    vx
    vy
    cG
    cbs
    cfv
    #
    cG
    cA
    @0
    @1
    eqidd
    cA
    cR
    cG
    cN
    cV
    matbas.a
    matbas.g
    matbas
    @0
    vx
    cv
    @1
    wcel
    vy
    cv
    @1
    wcel
    wa
    vx
    vy
    cG
    cplusg
    cfv
    cA
    cplusg
    cfv
    cA
    cR
    cG
    cN
    cV
    matbas.a
    matbas.g
    matplusg
    oveqdr
    grpinvpropd
end
