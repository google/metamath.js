include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "crp.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "elrp.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii2.mm"

theorem ralrp
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x e. RR+ ph <-> A. x e. RR ( 0 < x -> ph ) )

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
    wi
    #
    vx
    crp
    cr
    @0
    crp
    wcel
    #
    wph
    wi
    @0
    cr
    wcel
    #
    @1
    wa
    #
    wph
    wi
    @4
    @2
    wi
    @3
    @5
    wph
    @0
    elrp
    imbi1i
    @4
    @1
    wph
    impexp
    bitri
    ralbii2
end
