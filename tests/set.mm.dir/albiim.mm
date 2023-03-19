include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "dfbi2.mm"
include "albii.mm"
include "19.26.mm"
include "bitri.mm"

theorem albiim
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( A. x ( ph <-> ps ) <-> ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) )

  proof
    wph
    wps
    wb
    #
    vx
    wal
    wph
    wps
    wi
    #
    wps
    wph
    wi
    #
    wa
    #
    vx
    wal
    @1
    vx
    wal
    @2
    vx
    wal
    wa
    @0
    @3
    vx
    wph
    wps
    dfbi2
    albii
    @1
    @2
    vx
    19.26
    bitri
end
