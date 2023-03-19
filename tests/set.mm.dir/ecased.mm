include "wn.mm"
include "wo.mm"
include "wa.mm"
include "pm3.11.mm"
include "syl5.mm"
include "ecase3d.mm"

theorem ecased
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ecased.1: |- ( ph -> ( -. ps -> th ) )
  assume ecased.2: |- ( ph -> ( -. ch -> th ) )
  assume ecased.3: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wn
    #
    wch
    wn
    #
    wth
    ecased.1
    ecased.2
    @0
    @1
    wo
    wn
    wps
    wch
    wa
    wph
    wth
    wps
    wch
    pm3.11
    ecased.3
    syl5
    ecase3d
end
