include "wex.mm"
include "wal.mm"
include "sp.mm"
include "eximi.mm"
include "syl.mm"
include "alrimiv.mm"

theorem ex-natded9.26-2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume ex-natded9.26.1: |- ( ph -> E. x A. y ps )

  disjoint x y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A. y E. x ps )

  proof
    wph
    wps
    vx
    wex
    #
    vy
    wph
    wps
    vy
    wal
    #
    vx
    wex
    @0
    ex-natded9.26.1
    @1
    wps
    vx
    wps
    vy
    sp
    eximi
    syl
    alrimiv
end
