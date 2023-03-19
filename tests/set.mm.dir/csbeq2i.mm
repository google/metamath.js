include "csb.mm"
include "wceq.mm"
include "wtru.mm"
include "a1i.mm"
include "csbeq2dv.mm"
include "trud.mm"

theorem csbeq2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume csbeq2i.1: |- B = C


  assert |- [_ A / x ]_ B = [_ A / x ]_ C

  proof
    vx
    cA
    cB
    csb
    vx
    cA
    cC
    csb
    wceq
    wtru
    vx
    cA
    cB
    cC
    cB
    cC
    wceq
    wtru
    csbeq2i.1
    a1i
    csbeq2dv
    trud
end
