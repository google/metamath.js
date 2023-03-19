include "w3a.mm"
include "wb.mm"
include "wi.mm"
include "bicom.mm"
include "imbi2.mm"
include "biimpcd.mm"
include "mpi.mm"
include "3expd.mm"
include "3impexp.mm"
include "biimpri.mm"
include "syl6ibr.mm"
include "impbii.mm"

theorem 3impexpbicom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <-> ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wta
    wb
    #
    wi
    #
    wph
    wps
    wch
    wta
    wth
    wb
    #
    wi
    wi
    wi
    #
    @2
    wph
    wps
    wch
    @3
    @2
    @1
    @3
    wb
    #
    @0
    @3
    wi
    #
    wth
    wta
    bicom
    #
    @5
    @2
    @6
    @1
    @3
    @0
    imbi2
    biimpcd
    mpi
    3expd
    @4
    @0
    @3
    @1
    @6
    @4
    wph
    wps
    wch
    @3
    3impexp
    biimpri
    @7
    syl6ibr
    impbii
end
