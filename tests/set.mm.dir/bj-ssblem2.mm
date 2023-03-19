include "weq.mm"
include "wi.mm"
include "equequ1.mm"
include "equequ2.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "alcomiw.mm"

theorem bj-ssblem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vz: setvar z

  disjoint x y
  disjoint t x
  disjoint t y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint t z
  disjoint ph z
  assert |- ( A. x A. y ( y = t -> ( x = y -> ph ) ) -> A. y A. x ( y = t -> ( x = y -> ph ) ) )

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
    wi
    vx
    vy
    vz
    vy
    vz
    weq
    #
    @0
    @3
    @2
    @5
    vy
    vz
    vt
    equequ1
    @6
    @1
    @4
    wph
    vy
    vz
    vx
    equequ2
    imbi1d
    imbi12d
    alcomiw
end
