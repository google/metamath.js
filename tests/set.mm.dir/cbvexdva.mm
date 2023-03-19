include "wex.mm"
include "wn.mm"
include "wal.mm"
include "weq.mm"
include "wa.mm"
include "notbid.mm"
include "cbvaldva.mm"
include "alnex.mm"
include "3bitr3g.mm"
include "con4bid.mm"

theorem cbvexdva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbvaldva.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )

  disjoint ps y
  disjoint ch x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( E. x ps <-> E. y ch ) )

  proof
    wph
    wps
    vx
    wex
    #
    wch
    vy
    wex
    #
    wph
    wps
    wn
    #
    vx
    wal
    wch
    wn
    #
    vy
    wal
    @0
    wn
    @1
    wn
    wph
    @2
    @3
    vx
    vy
    wph
    vx
    vy
    weq
    wa
    wps
    wch
    cbvaldva.1
    notbid
    cbvaldva
    wps
    vx
    alnex
    wch
    vy
    alnex
    3bitr3g
    con4bid
end
