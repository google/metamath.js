include "wmo.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "nfe1.mm"
include "moexex.mm"
include "expcom.mm"
include "19.8a.mm"
include "pm4.71ri.mm"
include "exbii.mm"
include "mobii.mm"
include "syl6ibr.mm"

theorem 2moswap
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) )

  proof
    wph
    vy
    wmo
    vx
    wal
    #
    wph
    vy
    wex
    #
    vx
    wmo
    #
    @1
    wph
    wa
    #
    vx
    wex
    #
    vy
    wmo
    #
    wph
    vx
    wex
    #
    vy
    wmo
    @2
    @0
    @5
    @1
    wph
    vx
    vy
    wph
    vy
    nfe1
    moexex
    expcom
    @6
    @4
    vy
    wph
    @3
    vx
    wph
    @1
    wph
    vy
    19.8a
    pm4.71ri
    exbii
    mobii
    syl6ibr
end
