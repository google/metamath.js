include "ccnv.mm"
include "wfun.mm"
include "cdif.mm"
include "cima.mm"
include "cin.mm"
include "imadif.mm"
include "difeq2d.mm"
include "eqtrd.mm"
include "dfin4.mm"
include "imaeq2i.mm"
include "3eqtr4g.mm"

theorem imain
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( Fun `' F -> ( F " ( A i^i B ) ) = ( ( F " A ) i^i ( F " B ) ) )

  proof
    cF
    ccnv
    wfun
    #
    cF
    cA
    cA
    cB
    cdif
    #
    cdif
    #
    cima
    #
    cF
    cA
    cima
    #
    @4
    cF
    cB
    cima
    #
    cdif
    #
    cdif
    #
    cF
    cA
    cB
    cin
    #
    cima
    @4
    @5
    cin
    @0
    @3
    @4
    cF
    @1
    cima
    #
    cdif
    @7
    cA
    @1
    cF
    imadif
    @0
    @9
    @6
    @4
    cA
    cB
    cF
    imadif
    difeq2d
    eqtrd
    @8
    @2
    cF
    cA
    cB
    dfin4
    imaeq2i
    @4
    @5
    dfin4
    3eqtr4g
end
