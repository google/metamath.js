include "wn.mm"
include "w3o.mm"
include "w3a.mm"
include "3anor.mm"
include "con2bii.mm"
include "bicomi.mm"

theorem 3ianor
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ( ph /\ ps /\ ch ) <-> ( -. ph \/ -. ps \/ -. ch ) )

  proof
    wph
    wn
    wps
    wn
    wch
    wn
    w3o
    #
    wph
    wps
    wch
    w3a
    #
    wn
    @1
    @0
    wph
    wps
    wch
    3anor
    con2bii
    bicomi
end
