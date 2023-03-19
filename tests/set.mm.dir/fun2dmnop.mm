include "wfun.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wn.mm"
include "fundif.mm"
include "fun2dmnop0.mm"
include "syl3an1.mm"

theorem fun2dmnop
  let cA: class A
  let cB: class B
  let cG: class G
  assume fun2dmnop.a: |- A e. _V
  assume fun2dmnop.b: |- B e. _V


  assert |- ( ( Fun G /\ A =/= B /\ { A , B } C_ dom G ) -> -. G e. ( _V X. _V ) )

  proof
    cG
    wfun
    cG
    c0
    csn
    #
    cdif
    wfun
    cA
    cB
    wne
    cA
    cB
    cpr
    cG
    cdm
    wss
    cG
    cvv
    cvv
    cxp
    wcel
    wn
    @0
    cG
    fundif
    cA
    cB
    cG
    fun2dmnop.a
    fun2dmnop.b
    fun2dmnop0
    syl3an1
end
