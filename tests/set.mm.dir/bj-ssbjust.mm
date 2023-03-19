include "weq.mm"
include "wi.mm"
include "wal.mm"
include "equequ1.mm"
include "equequ2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "imbi12d.mm"
include "cbvalvw.mm"

theorem bj-ssbjust
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint t y
  disjoint t z
  disjoint ph y
  disjoint ph z
  assert |- ( A. y ( y = t -> A. x ( x = y -> ph ) ) <-> A. z ( z = t -> A. x ( x = z -> ph ) ) )

  proof
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    vz
    vt
    weq
    #
    vx
    vz
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    vy
    vz
    vy
    vz
    weq
    #
    @0
    @4
    @3
    @7
    vy
    vz
    vt
    equequ1
    @8
    @2
    @6
    vx
    @8
    @1
    @5
    wph
    vy
    vz
    vx
    equequ2
    imbi1d
    albidv
    imbi12d
    cbvalvw
end
