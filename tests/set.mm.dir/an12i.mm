include "wa.mm"
include "an12.mm"
include "mpbir.mm"

theorem an12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume an12i.1: |- ( ph /\ ( ps /\ ch ) )


  assert |- ( ps /\ ( ph /\ ch ) )

  proof
    wps
    wph
    wch
    wa
    wa
    wph
    wps
    wch
    wa
    wa
    an12i.1
    wps
    wph
    wch
    an12
    mpbir
end
