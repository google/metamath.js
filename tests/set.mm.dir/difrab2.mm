include "crab.mm"
include "cdif.mm"
include "nfrab1.mm"
include "nfdif.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "eldif.mm"
include "anbi1i.mm"
include "andi.mm"
include "pm3.24.mm"
include "biorfi.mm"
include "ancom.mm"
include "3bitr2i.mm"
include "anbi2i.mm"
include "anass.mm"
include "3bitr4i.mm"
include "bitr4i.mm"
include "rabid.mm"
include "notbii.mm"
include "ianor.mm"
include "bitri.mm"
include "anbi12i.mm"
include "3bitr4ri.mm"
include "eqri.mm"

theorem difrab2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( { x e. A | ph } \ { x e. B | ph } ) = { x e. ( A \ B ) | ph }

  proof
    vx
    wph
    vx
    cA
    crab
    #
    wph
    vx
    cB
    crab
    #
    cdif
    #
    wph
    vx
    cA
    cB
    cdif
    #
    crab
    #
    vx
    @0
    @1
    wph
    vx
    cA
    nfrab1
    wph
    vx
    cB
    nfrab1
    nfdif
    wph
    vx
    @3
    nfrab1
    vx
    cv
    #
    @3
    wcel
    #
    wph
    wa
    #
    @5
    cA
    wcel
    #
    wph
    wa
    #
    @5
    cB
    wcel
    #
    wn
    #
    wph
    wn
    #
    wo
    #
    wa
    #
    @5
    @4
    wcel
    @5
    @2
    wcel
    #
    @7
    @8
    @11
    wa
    #
    wph
    wa
    #
    @14
    @6
    @16
    wph
    @5
    cA
    cB
    eldif
    anbi1i
    @8
    wph
    @13
    wa
    #
    wa
    @8
    @11
    wph
    wa
    #
    wa
    @14
    @17
    @18
    @19
    @8
    @18
    wph
    @11
    wa
    #
    wph
    @12
    wa
    #
    wo
    @20
    @19
    wph
    @11
    @12
    andi
    @21
    @20
    wph
    pm3.24
    biorfi
    wph
    @11
    ancom
    3bitr2i
    anbi2i
    @8
    wph
    @13
    anass
    @8
    @11
    wph
    anass
    3bitr4i
    bitr4i
    wph
    vx
    @3
    rabid
    @15
    @5
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wn
    #
    wa
    @14
    @5
    @0
    @1
    eldif
    @22
    @9
    @24
    @13
    wph
    vx
    cA
    rabid
    @24
    @10
    wph
    wa
    #
    wn
    @13
    @23
    @25
    wph
    vx
    cB
    rabid
    notbii
    @10
    wph
    ianor
    bitri
    anbi12i
    bitri
    3bitr4ri
    eqri
end
