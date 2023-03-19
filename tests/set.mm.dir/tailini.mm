include "cdir.mm"
include "wcel.mm"
include "wa.mm"
include "ctail.mm"
include "cfv.mm"
include "wbr.mm"
include "dirref.mm"
include "wb.mm"
include "eltail.mm"
include "3anidm23.mm"
include "mpbird.mm"

theorem tailini
  let cA: class A
  let cD: class D
  let cX: class X
  assume tailini.1: |- X = dom D


  assert |- ( ( D e. DirRel /\ A e. X ) -> A e. ( ( tail ` D ) ` A ) )

  proof
    cD
    cdir
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cA
    cA
    cD
    ctail
    cfv
    cfv
    wcel
    #
    cA
    cA
    cD
    wbr
    #
    cA
    cD
    cX
    tailini.1
    dirref
    @0
    @1
    @2
    @3
    wb
    cA
    cA
    cX
    cD
    cX
    tailini.1
    eltail
    3anidm23
    mpbird
end
