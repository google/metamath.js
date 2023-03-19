include "wxo.mm"
include "wo.mm"
include "xoror.mm"
include "ax-mp.mm"
include "mtpor.mm"

theorem mtpxor
  let wph: wff ph
  let wps: wff ps
  assume mtpxor.min: |- -. ph
  assume mtpxor.maj: |- ( ph \/_ ps )


  assert |- ps

  proof
    wph
    wps
    mtpxor.min
    wph
    wps
    wxo
    wph
    wps
    wo
    mtpxor.maj
    wph
    wps
    xoror
    ax-mp
    mtpor
end
