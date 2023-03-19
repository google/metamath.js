include "nf5i.mm"
include "sbf.mm"

theorem sbh
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sbh.1: |- ( ph -> A. x ph )


  assert |- ( [ y / x ] ph <-> ph )

  proof
    wph
    vx
    vy
    wph
    vx
    sbh.1
    nf5i
    sbf
end
