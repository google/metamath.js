include "wa.mm"
include "wmo.mm"
include "wi.mm"
include "ibar.mm"
include "mobid.mm"
include "biimprcd.mm"
include "wex.mm"
include "simpl.mm"
include "exlimi.mm"
include "exmo.mm"
include "ori.mm"
include "nsyl4.mm"
include "con1i.mm"
include "moan.mm"
include "ja.mm"
include "impbii.mm"

theorem moanim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume moanim.1: |- F/ x ph


  assert |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) )

  proof
    wph
    wps
    wa
    #
    vx
    wmo
    #
    wph
    wps
    vx
    wmo
    #
    wi
    wph
    @2
    @1
    wph
    wps
    @0
    vx
    moanim.1
    wph
    wps
    ibar
    mobid
    biimprcd
    wph
    @2
    @1
    @1
    wph
    @0
    vx
    wex
    #
    wph
    @1
    @0
    wph
    vx
    moanim.1
    wph
    wps
    simpl
    exlimi
    @3
    @1
    @0
    vx
    exmo
    ori
    nsyl4
    con1i
    wps
    wph
    vx
    moan
    ja
    impbii
end
