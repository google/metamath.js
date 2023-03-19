include "cep.mm"
include "wfr.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wbr.mm"
include "frirr.mm"
include "epel.mm"
include "sylnib.mm"
include "ralrimiva.mm"

theorem efrunt
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( _E Fr A -> A. x e. A -. x e. x )

  proof
    cA
    cep
    wfr
    #
    vx
    cv
    #
    @1
    wcel
    #
    wn
    vx
    cA
    @0
    @1
    cA
    wcel
    wa
    @1
    @1
    cep
    wbr
    @2
    cA
    @1
    cep
    frirr
    vx
    vx
    epel
    sylnib
    ralrimiva
end
