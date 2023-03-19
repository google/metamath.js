include "wo.mm"
include "wa.mm"
include "orc.mm"
include "olc.mm"
include "jaodan.mm"
include "anim2i.mm"
include "jaoi.mm"
include "impbii.mm"

theorem andi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    wo
    #
    wa
    #
    wph
    wps
    wa
    #
    wph
    wch
    wa
    #
    wo
    #
    wph
    wps
    @4
    wch
    @2
    @3
    orc
    @3
    @2
    olc
    jaodan
    @2
    @1
    @3
    wps
    @0
    wph
    wps
    wch
    orc
    anim2i
    wch
    @0
    wph
    wch
    wps
    olc
    anim2i
    jaoi
    impbii
end
