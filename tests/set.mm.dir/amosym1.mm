include "wfal.mm"
include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "df-mo.mm"
include "wn.mm"
include "mof.mm"
include "19.8a.mm"
include "notnotd.mm"
include "ax-mp.mm"
include "pm2.21i.mm"
include "notnoti.mm"
include "nex.mm"
include "eunex.mm"
include "mto.mm"
include "ja.mm"
include "sylbi.mm"

theorem amosym1
  let wph: wff ph
  let vx: setvar x


  assert |- ( E* x E* x F. -> E* x ph )

  proof
    wfal
    vx
    wmo
    #
    vx
    wmo
    @0
    vx
    wex
    #
    @0
    vx
    weu
    #
    wi
    wph
    vx
    wmo
    #
    @0
    vx
    df-mo
    @1
    @2
    @3
    @1
    wn
    #
    @3
    @0
    @4
    wn
    vx
    mof
    #
    @0
    @1
    @0
    vx
    19.8a
    notnotd
    ax-mp
    pm2.21i
    @2
    @3
    @2
    @0
    wn
    #
    vx
    wex
    @6
    vx
    @0
    @5
    notnoti
    nex
    @0
    vx
    eunex
    mto
    pm2.21i
    ja
    sylbi
end
