include "wrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wceq.mm"
include "wb.mm"
include "df-rmo.mm"
include "simprl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "anim1i.mm"
include "simpll.mm"
include "simplr.mm"
include "anbi12d.mm"
include "mob.mm"
include "syl3anc.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "sylanb.mm"

theorem rmob
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume rmoi.b: |- ( x = B -> ( ph <-> ps ) )
  assume rmoi.c: |- ( x = C -> ( ph <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ps x
  disjoint ch x
  assert |- ( ( E* x e. A ph /\ ( B e. A /\ ps ) ) -> ( B = C <-> ( C e. A /\ ch ) ) )

  proof
    wph
    vx
    cA
    wrmo
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    #
    cB
    cA
    wcel
    #
    wps
    wa
    #
    cB
    cC
    wceq
    #
    cC
    cA
    wcel
    #
    wch
    wa
    #
    wb
    #
    wph
    vx
    cA
    df-rmo
    @3
    @5
    wa
    #
    @7
    @6
    @8
    @10
    @4
    @6
    @7
    @3
    @4
    wps
    simprl
    #
    cB
    cC
    cA
    eleq1
    syl5ibcom
    @8
    @7
    wi
    @10
    @7
    wch
    simpl
    a1i
    @10
    @7
    @9
    @10
    @7
    wa
    @4
    @7
    wa
    @3
    @5
    @9
    @10
    @4
    @7
    @11
    anim1i
    @3
    @5
    @7
    simpll
    @3
    @5
    @7
    simplr
    @2
    @5
    @8
    vx
    cB
    cC
    cA
    cA
    @0
    cB
    wceq
    @1
    @4
    wph
    wps
    @0
    cB
    cA
    eleq1
    rmoi.b
    anbi12d
    @0
    cC
    wceq
    @1
    @7
    wph
    wch
    @0
    cC
    cA
    eleq1
    rmoi.c
    anbi12d
    mob
    syl3anc
    ex
    pm5.21ndd
    sylanb
end
