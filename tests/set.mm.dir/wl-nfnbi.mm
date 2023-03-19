include "wnf.mm"
include "wn.mm"
include "nfnt.mm"
include "notnotb.mm"
include "nfxfrd.mm"
include "impbii.mm"

theorem wl-nfnbi
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph <-> F/ x -. ph )

  proof
    wph
    vx
    wnf
    wph
    wn
    #
    vx
    wnf
    #
    wph
    vx
    nfnt
    wph
    @0
    wn
    @1
    vx
    wph
    notnotb
    @0
    vx
    nfnt
    nfxfrd
    impbii
end
