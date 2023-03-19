include "wex.mm"
include "cab.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "abn0.mm"
include "intex.mm"
include "bitr3i.mm"

theorem intexab
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x ph <-> |^| { x | ph } e. _V )

  proof
    wph
    vx
    wex
    wph
    vx
    cab
    #
    c0
    wne
    @0
    cint
    cvv
    wcel
    wph
    vx
    abn0
    @0
    intex
    bitr3i
end
