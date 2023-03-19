include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wb.mm"
include "wrmo.mm"
include "df-rmo.mm"
include "sylib.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "mob2.mm"
include "syl112anc.mm"
include "mpbirand.mm"

theorem rmob2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rmoi2.1: |- ( x = B -> ( ps <-> ch ) )
  assume rmoi2.2: |- ( ph -> B e. A )
  assume rmoi2.3: |- ( ph -> E* x e. A ps )
  assume rmoi2.4: |- ( ph -> x e. A )
  assume rmoi2.5: |- ( ph -> ps )

  disjoint A x
  disjoint B x
  disjoint ch x
  assert |- ( ph -> ( x = B <-> ch ) )

  proof
    wph
    vx
    cv
    #
    cB
    wceq
    #
    cB
    cA
    wcel
    #
    wch
    rmoi2.2
    wph
    @2
    @0
    cA
    wcel
    #
    wps
    wa
    #
    vx
    wmo
    #
    @3
    wps
    @1
    @2
    wch
    wa
    #
    wb
    rmoi2.2
    wph
    wps
    vx
    cA
    wrmo
    @5
    rmoi2.3
    wps
    vx
    cA
    df-rmo
    sylib
    rmoi2.4
    rmoi2.5
    @4
    @6
    vx
    cB
    cA
    @1
    @3
    @2
    wps
    wch
    @0
    cB
    cA
    eleq1
    rmoi2.1
    anbi12d
    mob2
    syl112anc
    mpbirand
end
