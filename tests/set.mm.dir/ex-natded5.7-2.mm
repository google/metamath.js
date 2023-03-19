include "wa.mm"
include "wo.mm"
include "simpl.mm"
include "orim2i.mm"
include "syl.mm"

theorem ex-natded5.7-2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ex-natded5.7.1: |- ( ph -> ( ps \/ ( ch /\ th ) ) )


  assert |- ( ph -> ( ps \/ ch ) )

  proof
    wph
    wps
    wch
    wth
    wa
    #
    wo
    wps
    wch
    wo
    ex-natded5.7.1
    @0
    wch
    wps
    wch
    wth
    simpl
    orim2i
    syl
end
