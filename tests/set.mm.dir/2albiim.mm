include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "albiim.mm"
include "albii.mm"
include "19.26.mm"
include "bitri.mm"

theorem 2albiim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph <-> ps ) <-> ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) )

  proof
    wph
    wps
    wb
    vy
    wal
    #
    vx
    wal
    wph
    wps
    wi
    vy
    wal
    #
    wps
    wph
    wi
    vy
    wal
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
    vy
    albiim
    albii
    @1
    @2
    vx
    19.26
    bitri
end
