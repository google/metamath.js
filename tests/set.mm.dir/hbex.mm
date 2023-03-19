include "wex.mm"
include "nf5i.mm"
include "nfex.mm"
include "nf5ri.mm"

theorem hbex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume hbex.1: |- ( ph -> A. x ph )


  assert |- ( E. y ph -> A. x E. y ph )

  proof
    wph
    vy
    wex
    vx
    wph
    vx
    vy
    wph
    vx
    hbex.1
    nf5i
    nfex
    nf5ri
end
