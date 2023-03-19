include "wa.mm"
include "weu.mm"
include "wex.mm"
include "euex.mm"
include "simpl.mm"
include "exlimi.mm"
include "syl.mm"
include "ibar.mm"
include "eubid.mm"
include "biimprcd.mm"
include "jcai.mm"
include "biimpa.mm"
include "impbii.mm"

theorem euan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume moanim.1: |- F/ x ph


  assert |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) )

  proof
    wph
    wps
    wa
    #
    vx
    weu
    #
    wph
    wps
    vx
    weu
    #
    wa
    @1
    wph
    @2
    @1
    @0
    vx
    wex
    wph
    @0
    vx
    euex
    @0
    wph
    vx
    moanim.1
    wph
    wps
    simpl
    exlimi
    syl
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
    eubid
    #
    biimprcd
    jcai
    wph
    @2
    @1
    @3
    biimpa
    impbii
end
