include "nf5i.mm"
include "19.9.mm"

theorem 19.9h
  let wph: wff ph
  let vx: setvar x
  assume 19.9h.1: |- ( ph -> A. x ph )


  assert |- ( E. x ph <-> ph )

  proof
    wph
    vx
    wph
    vx
    19.9h.1
    nf5i
    19.9
end
