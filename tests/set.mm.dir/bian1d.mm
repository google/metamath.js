include "wa.mm"
include "biimpd.mm"
include "adantld.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "biimprd.mm"
include "jcad.mm"
include "impbid.mm"

theorem bian1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bian1d.1: |- ( ph -> ( ps <-> ( ch /\ th ) ) )


  assert |- ( ph -> ( ( ch /\ ps ) <-> ( ch /\ th ) ) )

  proof
    wph
    wch
    wps
    wa
    wch
    wth
    wa
    #
    wph
    wps
    @0
    wch
    wph
    wps
    @0
    bian1d.1
    biimpd
    adantld
    wph
    @0
    wch
    wps
    @0
    wch
    wi
    wph
    wch
    wth
    simpl
    a1i
    wph
    wps
    @0
    bian1d.1
    biimprd
    jcad
    impbid
end
