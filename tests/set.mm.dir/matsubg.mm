include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "matbas.mm"
include "matplusg.mm"
include "grpsubpropd.mm"

theorem matsubg
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cV: class V
  assume matsubg.a: |- A = ( N Mat R )
  assume matsubg.g: |- G = ( R freeLMod ( N X. N ) )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( -g ` G ) = ( -g ` A ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    wa
    cG
    cA
    cA
    cR
    cG
    cN
    cV
    matsubg.a
    matsubg.g
    matbas
    cA
    cR
    cG
    cN
    cV
    matsubg.a
    matsubg.g
    matplusg
    grpsubpropd
end
