include "wn.mm"
include "wa.mm"
include "niabn.mm"
include "bicomd.mm"

theorem ninba
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ninba.1: |- ph


  assert |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) )

  proof
    wps
    wn
    wch
    wps
    wa
    wph
    wn
    wph
    wps
    wch
    ninba.1
    niabn
    bicomd
end
