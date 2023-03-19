include "wfal.mm"
include "fal.mm"
include "2false.mm"

theorem bifal
  let wph: wff ph
  assume bifal.1: |- -. ph


  assert |- ( ph <-> F. )

  proof
    wph
    wfal
    bifal.1
    fal
    2false
end
