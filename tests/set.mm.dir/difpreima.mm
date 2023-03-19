include "wfun.mm"
include "ccnv.mm"
include "cdif.mm"
include "cima.mm"
include "wceq.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "syl.mm"

theorem difpreima
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( Fun F -> ( `' F " ( A \ B ) ) = ( ( `' F " A ) \ ( `' F " B ) ) )

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
    cdif
    cima
    @0
    cA
    cima
    @0
    cB
    cima
    cdif
    wceq
    cF
    funcnvcnv
    cA
    cB
    @0
    imadif
    syl
end
