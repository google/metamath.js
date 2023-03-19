include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "wb.mm"
include "nfv.mm"
include "nfth.mm"
include "sbc2iegf.mm"
include "mp2an.mm"

theorem sbc2ie
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume sbc2ie.1: |- A e. _V
  assume sbc2ie.2: |- B e. _V
  assume sbc2ie.3: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( [. A / x ]. [. B / y ]. ph <-> ps )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    #
    wph
    vy
    cB
    wsbc
    vx
    cA
    wsbc
    wps
    wb
    sbc2ie.1
    sbc2ie.2
    wph
    wps
    vx
    vy
    cA
    cB
    cvv
    cvv
    wps
    vx
    nfv
    wps
    vy
    nfv
    @0
    vx
    sbc2ie.2
    nfth
    sbc2ie.3
    sbc2iegf
    mp2an
end
