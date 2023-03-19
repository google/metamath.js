include "wfn.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "wrel.mm"
include "fnrel.mm"
include "releldm.mm"
include "sylan.mm"
include "fndm.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "syldan.mm"

theorem fnbr
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F Fn A /\ B F C ) -> B e. A )

  proof
    cF
    cA
    wfn
    #
    cB
    cC
    cF
    wbr
    #
    cB
    cF
    cdm
    #
    wcel
    #
    cB
    cA
    wcel
    #
    @0
    cF
    wrel
    @1
    @3
    cA
    cF
    fnrel
    cB
    cC
    cF
    releldm
    sylan
    @0
    @3
    @4
    @0
    @2
    cA
    cB
    cA
    cF
    fndm
    eleq2d
    biimpa
    syldan
end
