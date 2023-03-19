include "wfun.mm"
include "ccnv.mm"
include "cin.mm"
include "cima.mm"
include "wceq.mm"
include "funcnvcnv.mm"
include "imain.mm"
include "syl.mm"

theorem inpreima
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( Fun F -> ( `' F " ( A i^i B ) ) = ( ( `' F " A ) i^i ( `' F " B ) ) )

  proof
    cF
    wfun
    cF
    ccnv
    #
    ccnv
    wfun
    @0
    cA
    cB
    cin
    cima
    @0
    cA
    cima
    @0
    cB
    cima
    cin
    wceq
    cF
    funcnvcnv
    cA
    cB
    @0
    imain
    syl
end
