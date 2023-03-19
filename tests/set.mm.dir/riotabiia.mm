include "cvv.mm"
include "wceq.mm"
include "crio.mm"
include "eqid.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "adantl.mm"
include "riotabidva.mm"
include "ax-mp.mm"

theorem riotabiia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume riotabiia.1: |- ( x e. A -> ( ph <-> ps ) )


  assert |- ( iota_ x e. A ph ) = ( iota_ x e. A ps )

  proof
    cvv
    cvv
    wceq
    #
    wph
    vx
    cA
    crio
    wps
    vx
    cA
    crio
    wceq
    cvv
    eqid
    @0
    wph
    wps
    vx
    cA
    vx
    cv
    cA
    wcel
    wph
    wps
    wb
    @0
    riotabiia.1
    adantl
    riotabidva
    ax-mp
end
