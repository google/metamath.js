include "wex.mm"
include "weu.mm"
include "wmo.mm"
include "wa.mm"
include "eu5.mm"
include "excom.mm"
include "nfe1.mm"
include "nfmo.mm"
include "wi.mm"
include "19.8a.mm"
include "moimi.mm"
include "df-mo.mm"
include "sylib.mm"
include "eximd.mm"
include "syl5bi.mm"
include "impcom.mm"
include "sylbi.mm"

theorem 2euex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x E. y ph -> E. y E! x ph )

  proof
    wph
    vy
    wex
    #
    vx
    weu
    @0
    vx
    wex
    #
    @0
    vx
    wmo
    #
    wa
    wph
    vx
    weu
    #
    vy
    wex
    #
    @0
    vx
    eu5
    @2
    @1
    @4
    @1
    wph
    vx
    wex
    #
    vy
    wex
    @2
    @4
    wph
    vx
    vy
    excom
    @2
    @5
    @3
    vy
    @0
    vy
    vx
    wph
    vy
    nfe1
    nfmo
    @2
    wph
    vx
    wmo
    @5
    @3
    wi
    wph
    @0
    vx
    wph
    vy
    19.8a
    moimi
    wph
    vx
    df-mo
    sylib
    eximd
    syl5bi
    impcom
    sylbi
end
