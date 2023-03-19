include "wsb.mm"
include "sbco.mm"
include "sbf.mm"
include "bitri.mm"

theorem sbid2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sbid2.1: |- F/ x ph


  assert |- ( [ y / x ] [ x / y ] ph <-> ph )

  proof
    wph
    vy
    vx
    wsb
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    wph
    wph
    vx
    vy
    sbco
    wph
    vx
    vy
    sbid2.1
    sbf
    bitri
end
