include "co.mm"
include "crn.mm"
include "cuni.mm"
include "ovssunirn.mm"
include "arwval.mm"
include "sseqtr4i.mm"

theorem homarw
  let cA: class A
  let cC: class C
  let cH: class H
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assume arwrcl.a: |- A = ( Arrow ` C )
  assume arwhoma.h: |- H = ( HomA ` C )


  assert |- ( X H Y ) C_ A

  proof
    cX
    cY
    cH
    co
    cH
    crn
    cuni
    cA
    cH
    cX
    cY
    ovssunirn
    cA
    cC
    cH
    arwrcl.a
    arwhoma.h
    arwval
    sseqtr4i
end
