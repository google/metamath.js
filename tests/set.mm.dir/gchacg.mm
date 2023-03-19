include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cgch.mm"
include "wcel.mm"
include "cpw.mm"
include "w3a.mm"
include "char.mm"
include "cfv.mm"
include "con0.mm"
include "cen.mm"
include "ccrd.mm"
include "cdm.mm"
include "harcl.mm"
include "gchhar.mm"
include "isnumi.mm"
include "sylancr.mm"

theorem gchacg
  let cA: class A


  assert |- ( ( _om ~<_ A /\ A e. GCH /\ ~P A e. GCH ) -> ~P A e. dom card )

  proof
    com
    cA
    cdom
    wbr
    cA
    cgch
    wcel
    cA
    cpw
    #
    cgch
    wcel
    w3a
    cA
    char
    cfv
    #
    con0
    wcel
    @1
    @0
    cen
    wbr
    @0
    ccrd
    cdm
    wcel
    cA
    harcl
    cA
    gchhar
    @1
    @0
    isnumi
    sylancr
end
