include "wo.mm"
include "orc.mm"
include "olcd.mm"
include "olc.mm"
include "orim2i.mm"
include "jaoi.mm"

theorem pm1.5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) )

  proof
    wph
    wps
    wph
    wch
    wo
    #
    wo
    wps
    wch
    wo
    wph
    @0
    wps
    wph
    wch
    orc
    olcd
    wch
    @0
    wps
    wch
    wph
    olc
    orim2i
    jaoi
end
