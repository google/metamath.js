include "wal.mm"
include "wi.mm"
include "weq.mm"
include "wb.mm"
include "expcom.mm"
include "pm5.74d.mm"
include "cbvalv.mm"
include "19.21v.mm"
include "3bitr3i.mm"
include "pm5.74ri.mm"

theorem cbvaldva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbvaldva.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )

  disjoint ps y
  disjoint ch x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    wps
    vx
    wal
    #
    wch
    vy
    wal
    #
    wph
    wps
    wi
    #
    vx
    wal
    wph
    wch
    wi
    #
    vy
    wal
    wph
    @0
    wi
    wph
    @1
    wi
    @2
    @3
    vx
    vy
    vx
    vy
    weq
    #
    wph
    wps
    wch
    wph
    @4
    wps
    wch
    wb
    cbvaldva.1
    expcom
    pm5.74d
    cbvalv
    wph
    wps
    vx
    19.21v
    wph
    wch
    vy
    19.21v
    3bitr3i
    pm5.74ri
end
