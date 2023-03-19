include "wxo.mm"
include "wa.mm"
include "wn.mm"
include "xornan.mm"
include "ax-mp.mm"
include "mptnan.mm"

theorem mptxor
  let wph: wff ph
  let wps: wff ps
  assume mptxor.min: |- ph
  assume mptxor.maj: |- ( ph \/_ ps )


  assert |- -. ps

  proof
    wph
    wps
    mptxor.min
    wph
    wps
    wxo
    wph
    wps
    wa
    wn
    mptxor.maj
    wph
    wps
    xornan
    ax-mp
    mptnan
end
