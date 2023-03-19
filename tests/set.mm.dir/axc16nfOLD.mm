include "weq.mm"
include "wal.mm"
include "wnf.mm"
include "aev.mm"
include "nfa1.mm"
include "axc16.mm"
include "nf5d.mm"
include "syl.mm"

theorem axc16nfOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint w z
  assert |- ( A. x x = y -> F/ z ph )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vw
    weq
    #
    vz
    wal
    #
    wph
    vz
    wnf
    vx
    vy
    vz
    vw
    vz
    aev
    @1
    wph
    vz
    @0
    vz
    nfa1
    wph
    vz
    vw
    axc16
    nf5d
    syl
end
