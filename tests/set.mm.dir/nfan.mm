include "wa.mm"
include "wnf.mm"
include "wtru.mm"
include "a1i.mm"
include "nfand.mm"
include "trud.mm"

theorem nfan
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume nfan.1: |- F/ x ph
  assume nfan.2: |- F/ x ps


  assert |- F/ x ( ph /\ ps )

  proof
    wph
    wps
    wa
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
    nfan.1
    a1i
    wps
    vx
    wnf
    wtru
    nfan.2
    a1i
    nfand
    trud
end
