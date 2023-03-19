include "com.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "csn.mm"
include "snelpwi.mm"
include "snfi.mm"
include "a1i.mm"
include "elind.mm"

theorem ackbij1lem4
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cH: class H
  let cB: class B


  assert |- ( A e. _om -> { A } e. ( ~P _om i^i Fin ) )

  proof
    cA
    com
    wcel
    #
    com
    cpw
    cfn
    cA
    csn
    #
    cA
    com
    snelpwi
    @1
    cfn
    wcel
    @0
    cA
    snfi
    a1i
    elind
end
