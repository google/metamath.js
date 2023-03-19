include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cop.mm"
include "funfvop.mm"
include "df-br.mm"
include "sylibr.mm"
include "wrel.mm"
include "funrel.mm"
include "releldm.mm"
include "sylan.mm"
include "impbida.mm"

theorem funfvbrb
  let cA: class A
  let cF: class F


  assert |- ( Fun F -> ( A e. dom F <-> A F ( F ` A ) ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    wcel
    #
    cA
    cA
    cF
    cfv
    #
    cF
    wbr
    #
    @0
    @1
    wa
    cA
    @2
    cop
    cF
    wcel
    @3
    cA
    cF
    funfvop
    cA
    @2
    cF
    df-br
    sylibr
    @0
    cF
    wrel
    @3
    @1
    cF
    funrel
    cA
    @2
    cF
    releldm
    sylan
    impbida
end
