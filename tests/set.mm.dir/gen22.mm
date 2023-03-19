include "wal.mm"
include "dfvd2i.mm"
include "alrimdv.mm"
include "dfvd2ir.mm"

theorem gen22
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume gen22.1: |- (. ph ,. ps ->. ch ).

  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps y
  assert |- (. ph ,. ps ->. A. x A. y ch ).

  proof
    wph
    wps
    wch
    vy
    wal
    #
    vx
    wal
    wph
    wps
    @0
    vx
    wph
    wps
    wch
    vy
    wph
    wps
    wch
    gen22.1
    dfvd2i
    alrimdv
    alrimdv
    dfvd2ir
end
