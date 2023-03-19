include "wb.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "pm5.18.mm"
include "biimpi.mm"
include "imnan.mm"
include "mpbi.mm"

theorem pm5.16
  let wph: wff ph
  let wps: wff ps


  assert |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wn
    wb
    #
    wn
    #
    wi
    @0
    @1
    wa
    wn
    @0
    @2
    wph
    wps
    pm5.18
    biimpi
    @0
    @1
    imnan
    mpbi
end
