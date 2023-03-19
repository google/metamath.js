include "nfiOLD.mm"
include "19.9OLD.mm"

theorem 19.9hOLD
  let wph: wff ph
  let vx: setvar x
  assume 19.9hOLD.1: |- ( ph -> A. x ph )


  assert |- ( E. x ph <-> ph )

  proof
    wph
    vx
    wph
    vx
    19.9hOLD.1
    nfiOLD
    19.9OLD
end
