include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wb.mm"
include "orel2.mm"
include "orc.mm"
include "impbid1.mm"
include "anbi1d.mm"
include "pm2.21.mm"
include "pm5.32rd.mm"
include "ja.mm"

theorem pm5.71
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <-> ( ph /\ ch ) ) )

  proof
    wps
    wch
    wn
    #
    wph
    wps
    wo
    #
    wch
    wa
    wph
    wch
    wa
    wb
    wps
    wn
    #
    @1
    wph
    wch
    @2
    @1
    wph
    wps
    wph
    orel2
    wph
    wps
    orc
    impbid1
    anbi1d
    @0
    wch
    @1
    wph
    wch
    @1
    wph
    wb
    pm2.21
    pm5.32rd
    ja
end
