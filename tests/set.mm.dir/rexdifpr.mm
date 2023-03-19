include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "eldifpr.mm"
include "3anass.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "df-3an.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "rexbii2.mm"

theorem rexdifpr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( E. x e. ( A \ { B , C } ) ph <-> E. x e. A ( x =/= B /\ x =/= C /\ ph ) )

  proof
    wph
    vx
    cv
    #
    cB
    wne
    #
    @0
    cC
    wne
    #
    wph
    w3a
    #
    vx
    cA
    cB
    cC
    cpr
    cdif
    #
    cA
    @0
    @4
    wcel
    #
    wph
    wa
    @0
    cA
    wcel
    #
    @1
    @2
    wa
    #
    wa
    #
    wph
    wa
    #
    @6
    @3
    wa
    #
    @5
    @8
    wph
    @5
    @6
    @1
    @2
    w3a
    @8
    @0
    cA
    cB
    cC
    eldifpr
    @6
    @1
    @2
    3anass
    bitri
    anbi1i
    @9
    @6
    @7
    wph
    wa
    #
    wa
    @10
    @6
    @7
    wph
    anass
    @11
    @3
    @6
    @3
    @11
    @1
    @2
    wph
    df-3an
    bicomi
    anbi2i
    bitri
    bitri
    rexbii2
end
