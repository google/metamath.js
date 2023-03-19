include "wa.mm"
include "wn.mm"
include "wo.mm"
include "ianor.mm"
include "anbi2i.mm"
include "andi.mm"
include "pm3.24.mm"
include "pm2.21i.mm"
include "id.mm"
include "jaoi.mm"
include "olc.mm"
include "impbii.mm"
include "3bitri.mm"

theorem annotanannotOLD
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ -. ( ph /\ ps ) ) <-> ( ph /\ -. ps ) )

  proof
    wph
    wph
    wps
    wa
    wn
    #
    wa
    wph
    wph
    wn
    #
    wps
    wn
    #
    wo
    #
    wa
    wph
    @1
    wa
    #
    wph
    @2
    wa
    #
    wo
    #
    @5
    @0
    @3
    wph
    wph
    wps
    ianor
    anbi2i
    wph
    @1
    @2
    andi
    @6
    @5
    @4
    @5
    @5
    @4
    @5
    wph
    pm3.24
    pm2.21i
    @5
    id
    jaoi
    @5
    @4
    olc
    impbii
    3bitri
end
