include "wi.mm"
include "wfal.mm"
include "falim.mm"
include "pm2.04.mm"
include "mpi.mm"
include "jarl.mm"
include "idd.mm"
include "jad.mm"
include "looinv.mm"
include "3syl.mm"
include "a1dd.mm"
include "a1i.mm"
include "com4l.mm"

theorem merco2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph -> ps ) -> ( ( F. -> ch ) -> th ) ) -> ( ( th -> ph ) -> ( ta -> ( et -> ph ) ) ) )

  proof
    wet
    wph
    wps
    wi
    #
    wfal
    wch
    wi
    #
    wth
    wi
    wi
    #
    wth
    wph
    wi
    #
    wta
    wph
    @2
    @3
    wta
    wph
    wi
    wi
    wi
    wet
    @2
    @3
    wph
    wta
    @2
    @0
    wth
    wi
    #
    wph
    wth
    wi
    wth
    wi
    @3
    wph
    wi
    @2
    @1
    @4
    wch
    falim
    @0
    @1
    wth
    pm2.04
    mpi
    @4
    wph
    wth
    wth
    wph
    wps
    wth
    jarl
    @4
    wth
    idd
    jad
    wph
    wth
    looinv
    3syl
    a1dd
    a1i
    com4l
end
