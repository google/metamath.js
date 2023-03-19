include "wcel.mm"
include "cfin3.mm"
include "com.mm"
include "cwdom.mm"
include "wbr.mm"
include "wn.mm"
include "isfin32i.mm"
include "isf33lem.mm"
include "isf32lem12.mm"
include "impbid2.mm"

theorem isfin3-2
  let cA: class A
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( A e. V -> ( A e. Fin3 <-> -. _om ~<_* A ) )

  proof
    cA
    cV
    wcel
    cA
    cfin3
    wcel
    com
    cA
    cwdom
    wbr
    wn
    cA
    isfin32i
    vx
    vg
    cfin3
    cA
    cV
    va
    vx
    vg
    va
    isf33lem
    isf32lem12
    impbid2
end
