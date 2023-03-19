include "cv.mm"
include "co.mm"
include "oveq1.mm"
include "nmfval.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem nmval
  let cA: class A
  let cD: class D
  let cN: class N
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vw: setvar w
  assume nmfval.n: |- N = ( norm ` W )
  assume nmfval.x: |- X = ( Base ` W )
  assume nmfval.z: |- .0. = ( 0g ` W )
  assume nmfval.d: |- D = ( dist ` W )


  assert |- ( A e. X -> ( N ` A ) = ( A D .0. ) )

  proof
    vx
    cA
    vx
    cv
    #
    c.0
    cD
    co
    cA
    c.0
    cD
    co
    cX
    cN
    @0
    cA
    c.0
    cD
    oveq1
    vx
    cD
    cN
    cW
    cX
    c.0
    nmfval.n
    nmfval.x
    nmfval.z
    nmfval.d
    nmfval
    cA
    c.0
    cD
    ovex
    fvmpt
end
