include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elisset.mm"
include "anim12i.mm"
include "eeanv.mm"
include "sylibr.mm"
include "biimprcd.mm"
include "2eximdv.mm"
include "syl5com.mm"

theorem spc2egv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume spc2egv.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( ( A e. V /\ B e. W ) -> ( ps -> E. x E. y ph ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    cB
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    wps
    wph
    vy
    wex
    vx
    wex
    @2
    @3
    vx
    wex
    #
    @4
    vy
    wex
    #
    wa
    @6
    @0
    @7
    @1
    @8
    vx
    cA
    cV
    elisset
    vy
    cB
    cW
    elisset
    anim12i
    @3
    @4
    vx
    vy
    eeanv
    sylibr
    wps
    @5
    wph
    vx
    vy
    @5
    wph
    wps
    spc2egv.1
    biimprcd
    2eximdv
    syl5com
end
