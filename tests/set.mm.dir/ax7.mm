include "weq.mm"
include "wi.mm"
include "ax7v2.mm"
include "wa.mm"
include "ax7v1.mm"
include "imp.mm"
include "a1i.mm"
include "syl2and.mm"
include "expd.mm"
include "ax6evr.mm"
include "exlimiiv.mm"

theorem ax7
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  let vt: setvar t


  assert |- ( x = y -> ( x = z -> y = z ) )

  proof
    vx
    vt
    weq
    #
    vx
    vy
    weq
    #
    vx
    vz
    weq
    #
    vy
    vz
    weq
    #
    wi
    wi
    vt
    @0
    @1
    @2
    @3
    @0
    @1
    vt
    vy
    weq
    #
    @2
    vt
    vz
    weq
    #
    @3
    vx
    vt
    vy
    ax7v2
    vx
    vt
    vz
    ax7v2
    @4
    @5
    wa
    @3
    wi
    @0
    @4
    @5
    @3
    vt
    vy
    vz
    ax7v1
    imp
    a1i
    syl2and
    expd
    vt
    vx
    ax6evr
    exlimiiv
end
