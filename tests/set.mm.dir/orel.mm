include "wa.mm"
include "simprl.mm"
include "ancoms.mm"
include "sylan.mm"
include "simprr.mm"
include "wo.mm"
include "adantr.mm"
include "mpjaodan.mm"

theorem orel
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wet: wff et
  let wrh: wff rh
  assume orel.1: |- ( ( ps /\ et ) -> th )
  assume orel.2: |- ( ( ch /\ rh ) -> th )
  assume orel.3: |- ( ph -> ( ps \/ ch ) )


  assert |- ( ( ph /\ ( et /\ rh ) ) -> th )

  proof
    wph
    wet
    wrh
    wa
    #
    wa
    #
    wps
    wth
    wch
    @1
    wet
    wps
    wth
    wph
    wet
    wrh
    simprl
    wps
    wet
    wth
    orel.1
    ancoms
    sylan
    @1
    wrh
    wch
    wth
    wph
    wet
    wrh
    simprr
    wch
    wrh
    wth
    orel.2
    ancoms
    sylan
    wph
    wps
    wch
    wo
    @0
    orel.3
    adantr
    mpjaodan
end
