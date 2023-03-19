include "wceq.mm"
include "wsbc.mm"
include "csb.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "sbceqg.mm"
include "ax-mp.mm"
include "eqeq12i.mm"
include "bitri.mm"

theorem sbceqi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume sbceqi.1: |- A e. _V
  assume sbceqi.2: |- [_ A / x ]_ B = D
  assume sbceqi.3: |- [_ A / x ]_ C = E


  assert |- ( [. A / x ]. B = C <-> D = E )

  proof
    cB
    cC
    wceq
    vx
    cA
    wsbc
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    wceq
    #
    cD
    cE
    wceq
    cA
    cvv
    wcel
    @0
    @3
    wb
    sbceqi.1
    vx
    cA
    cB
    cC
    cvv
    sbceqg
    ax-mp
    @1
    cD
    @2
    cE
    sbceqi.2
    sbceqi.3
    eqeq12i
    bitri
end
