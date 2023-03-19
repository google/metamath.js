include "wb.mm"
include "wnf.mm"
include "wtru.mm"
include "a1i.mm"
include "nfbid.mm"
include "trud.mm"

theorem nfbi
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume nf.1: |- F/ x ph
  assume nf.2: |- F/ x ps


  assert |- F/ x ( ph <-> ps )

  proof
    wph
    wps
    wb
    vx
    wnf
    wtru
    wph
    wps
    vx
    wph
    vx
    wnf
    wtru
    nf.1
    a1i
    wps
    vx
    wnf
    wtru
    nf.2
    a1i
    nfbid
    trud
end
