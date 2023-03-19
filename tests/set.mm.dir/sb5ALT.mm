include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "equsb1.mm"
include "sban.mm"
include "simplbi2com.mm"
include "mpi.mm"
include "spsbe.mm"
include "syl.mm"
include "hbs1.mm"
include "wi.mm"
include "simpr.mm"
include "a1i.mm"
include "simpl.mm"
include "sbequ1.mm"
include "com12.mm"
include "syl6c.mm"
include "exlimexi.mm"
include "impbii.mm"

theorem sb5ALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) )

  proof
    wph
    vx
    vy
    wsb
    #
    vx
    vy
    weq
    #
    wph
    wa
    #
    vx
    wex
    #
    @0
    @2
    vx
    vy
    wsb
    #
    @3
    @0
    @1
    vx
    vy
    wsb
    #
    @4
    vx
    vy
    equsb1
    @4
    @5
    @0
    @1
    wph
    vx
    vy
    sban
    simplbi2com
    mpi
    @2
    vx
    vy
    spsbe
    syl
    @2
    @0
    vx
    wph
    vx
    vy
    hbs1
    @3
    @2
    wph
    @1
    @0
    @2
    wph
    wi
    @3
    @1
    wph
    simpr
    a1i
    @2
    @1
    wi
    @3
    @1
    wph
    simpl
    a1i
    @1
    wph
    @0
    wph
    vx
    vy
    sbequ1
    com12
    syl6c
    exlimexi
    impbii
end
