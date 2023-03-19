include "wa.mm"
include "wn.mm"
include "simpr.mm"
include "orim12i.mm"

theorem resolution
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) -> ( ps \/ ch ) )

  proof
    wph
    wps
    wa
    wps
    wph
    wn
    #
    wch
    wa
    wch
    wph
    wps
    simpr
    @0
    wch
    simpr
    orim12i
end
