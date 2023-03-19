include "wex.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "aaan.mm"
include "prth.mm"
include "2alimi.mm"
include "sylbir.mm"
include "nfex.mm"
include "exim.mm"
include "19.42v.mm"
include "3imtr3g.mm"
include "pm3.21.mm"
include "simpl.mm"
include "imim2i.mm"
include "syl9.mm"
include "syl5.mm"
include "alimd.mm"
include "adantl.mm"
include "ax-11.mm"
include "19.41v.mm"
include "pm3.2.mm"
include "simpr.mm"
include "adantr.mm"
include "jcad.mm"
include "impbid2.mm"

theorem pm11.71
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  disjoint ps y
  disjoint ch x
  disjoint th x
  assert |- ( ( E. x ph /\ E. y ch ) -> ( ( A. x ( ph -> ps ) /\ A. y ( ch -> th ) ) <-> A. x A. y ( ( ph /\ ch ) -> ( ps /\ th ) ) ) )

  proof
    wph
    vx
    wex
    #
    wch
    vy
    wex
    #
    wa
    #
    wph
    wps
    wi
    #
    vx
    wal
    #
    wch
    wth
    wi
    #
    vy
    wal
    #
    wa
    #
    wph
    wch
    wa
    #
    wps
    wth
    wa
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @7
    @3
    @5
    wa
    #
    vy
    wal
    vx
    wal
    @12
    @3
    @5
    vx
    vy
    @3
    vy
    nfv
    @5
    vx
    nfv
    aaan
    @13
    @10
    vx
    vy
    wph
    wps
    wch
    wth
    prth
    2alimi
    sylbir
    @2
    @12
    @4
    @6
    @1
    @12
    @4
    wi
    @0
    @1
    @11
    @3
    vx
    wch
    vx
    vy
    wch
    vx
    nfv
    nfex
    @11
    wph
    @1
    wa
    #
    wps
    wth
    vy
    wex
    #
    wa
    #
    wi
    #
    @1
    @3
    @11
    @8
    vy
    wex
    @9
    vy
    wex
    @14
    @16
    @8
    @9
    vy
    exim
    wph
    wch
    vy
    19.42v
    wps
    wth
    vy
    19.42v
    3imtr3g
    @1
    wph
    @14
    @17
    wps
    @1
    wph
    pm3.21
    @16
    wps
    @14
    wps
    @15
    simpl
    imim2i
    syl9
    syl5
    alimd
    adantl
    @0
    @12
    @6
    wi
    @1
    @12
    @10
    vx
    wal
    #
    vy
    wal
    @0
    @6
    @10
    vx
    vy
    ax-11
    @0
    @18
    @5
    vy
    wph
    vy
    vx
    wph
    vy
    nfv
    nfex
    @18
    @0
    wch
    wa
    #
    wps
    vx
    wex
    #
    wth
    wa
    #
    wi
    #
    @0
    @5
    @18
    @8
    vx
    wex
    @9
    vx
    wex
    @19
    @21
    @8
    @9
    vx
    exim
    wph
    wch
    vx
    19.41v
    wps
    wth
    vx
    19.41v
    3imtr3g
    @0
    wch
    @19
    @22
    wth
    @0
    wch
    pm3.2
    @21
    wth
    @19
    @20
    wth
    simpr
    imim2i
    syl9
    syl5
    alimd
    syl5
    adantr
    jcad
    impbid2
end
