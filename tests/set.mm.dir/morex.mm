include "wmo.mm"
include "wrex.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "exancom.mm"
include "bitri.mm"
include "wal.mm"
include "nfmo1.mm"
include "nfe1.mm"
include "nfan.mm"
include "mopick.mm"
include "alrimi.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcv.mm"
include "syl.mm"
include "sylan2b.mm"
include "ancoms.mm"

theorem morex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume morex.1: |- B e. _V
  assume morex.2: |- ( x = B -> ( ph <-> ps ) )

  disjoint B x
  disjoint A x
  disjoint ps x
  assert |- ( ( E. x e. A ph /\ E* x ph ) -> ( ps -> B e. A ) )

  proof
    wph
    vx
    wmo
    #
    wph
    vx
    cA
    wrex
    #
    wps
    cB
    cA
    wcel
    #
    wi
    #
    @1
    @0
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    vx
    wex
    #
    @3
    @1
    @5
    wph
    wa
    vx
    wex
    @7
    wph
    vx
    cA
    df-rex
    @5
    wph
    vx
    exancom
    bitri
    @0
    @7
    wa
    #
    wph
    @5
    wi
    #
    vx
    wal
    @3
    @8
    @9
    vx
    @0
    @7
    vx
    wph
    vx
    nfmo1
    @6
    vx
    nfe1
    nfan
    wph
    @5
    vx
    mopick
    alrimi
    @9
    @3
    vx
    cB
    morex.1
    @4
    cB
    wceq
    wph
    wps
    @5
    @2
    morex.2
    @4
    cB
    cA
    eleq1
    imbi12d
    spcv
    syl
    sylan2b
    ancoms
end
