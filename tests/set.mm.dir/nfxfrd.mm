include "wnf.mm"
include "nfbii.mm"
include "sylibr.mm"

theorem nfxfrd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume nfbii.1: |- ( ph <-> ps )
  assume nfxfrd.2: |- ( ch -> F/ x ps )


  assert |- ( ch -> F/ x ph )

  proof
    wch
    wps
    vx
    wnf
    wph
    vx
    wnf
    nfxfrd.2
    wph
    wps
    vx
    nfbii.1
    nfbii
    sylibr
end
