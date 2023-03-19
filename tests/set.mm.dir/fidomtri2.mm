include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "domnsym.mm"
include "cen.mm"
include "sdomdom.mm"
include "con3i.mm"
include "wb.mm"
include "fidomtri.mm"
include "ancoms.mm"
include "syl5ibr.mm"
include "wi.mm"
include "ensym.mm"
include "endom.mm"
include "syl.mm"
include "a1i.mm"
include "jcad.mm"
include "brsdom.mm"
include "syl6ibr.mm"
include "con1d.mm"
include "impbid2.mm"

theorem fidomtri2
  let cA: class A
  let cB: class B
  let cV: class V
  let vc: setvar c
  let vf: setvar f
  let va: setvar a


  assert |- ( ( A e. V /\ B e. Fin ) -> ( A ~<_ B <-> -. B ~< A ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    csdm
    wbr
    #
    wn
    cA
    cB
    domnsym
    @2
    @3
    @4
    @2
    @3
    wn
    #
    cB
    cA
    cdom
    wbr
    #
    cB
    cA
    cen
    wbr
    #
    wn
    #
    wa
    @4
    @2
    @5
    @6
    @8
    @5
    @6
    @2
    cA
    cB
    csdm
    wbr
    #
    wn
    #
    @9
    @3
    cA
    cB
    sdomdom
    con3i
    @1
    @0
    @6
    @10
    wb
    cB
    cA
    cV
    fidomtri
    ancoms
    syl5ibr
    @5
    @8
    wi
    @2
    @7
    @3
    @7
    cA
    cB
    cen
    wbr
    @3
    cB
    cA
    ensym
    cA
    cB
    endom
    syl
    con3i
    a1i
    jcad
    cB
    cA
    brsdom
    syl6ibr
    con1d
    impbid2
end
