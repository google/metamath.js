include "nfv.mm"
include "sbid2.mm"

theorem sbid2v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph x
  assert |- ( [ y / x ] [ x / y ] ph <-> ph )

  proof
    wph
    vx
    vy
    wph
    vx
    nfv
    sbid2
end
