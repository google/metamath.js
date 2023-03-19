include "c2o.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "com.mm"
include "oveq2.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem fin1a2lem3
  let vx: setvar x
  let cA: class A
  let cE: class E
  let va: setvar a
  let vf: setvar f
  let vy: setvar y
  let vb: setvar b
  let cS: class S
  assume fin1a2lem.b: |- E = ( x e. _om |-> ( 2o .o x ) )


  assert |- ( A e. _om -> ( E ` A ) = ( 2o .o A ) )

  proof
    va
    cA
    c2o
    va
    cv
    #
    comu
    co
    #
    c2o
    cA
    comu
    co
    com
    cE
    @0
    cA
    c2o
    comu
    oveq2
    cE
    vx
    com
    c2o
    vx
    cv
    #
    comu
    co
    #
    cmpt
    va
    com
    @1
    cmpt
    fin1a2lem.b
    vx
    va
    com
    @3
    @1
    @2
    @0
    c2o
    comu
    oveq2
    cbvmptv
    eqtri
    c2o
    cA
    comu
    ovex
    fvmpt
end
