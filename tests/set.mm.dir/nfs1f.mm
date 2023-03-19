include "wsb.mm"
include "sbf.mm"
include "nfxfr.mm"

theorem nfs1f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfs1f.1: |- F/ x ph


  assert |- F/ x [ y / x ] ph

  proof
    wph
    vx
    vy
    wsb
    wph
    vx
    wph
    vx
    vy
    nfs1f.1
    sbf
    nfs1f.1
    nfxfr
end
