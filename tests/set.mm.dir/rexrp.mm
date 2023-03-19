include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "cr.mm"
include "wcel.mm"
include "elrp.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"

theorem rexrp
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x e. RR+ ph <-> E. x e. RR ( 0 < x /\ ph ) )

  proof
    wph
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    wph
    wa
    #
    vx
    crp
    cr
    @0
    crp
    wcel
    #
    wph
    wa
    @0
    cr
    wcel
    #
    @1
    wa
    #
    wph
    wa
    @4
    @2
    wa
    @3
    @5
    wph
    @0
    elrp
    anbi1i
    @4
    @1
    wph
    anass
    bitri
    rexbii2
end
