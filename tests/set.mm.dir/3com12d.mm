include "w3a.mm"
include "id.mm"
include "3com12.mm"
include "syl.mm"

theorem 3com12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3com12d.1: |- ( ph -> ( ps /\ ch /\ th ) )


  assert |- ( ph -> ( ch /\ ps /\ th ) )

  proof
    wph
    wps
    wch
    wth
    w3a
    wch
    wps
    wth
    w3a
    #
    3com12d.1
    wch
    wps
    wth
    @0
    @0
    id
    3com12
    syl
end
