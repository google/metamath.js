include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "biimpa.mm"
include "exlimivv.mm"
include "cv.mm"
include "wceq.mm"
include "elisset.mm"
include "anim12i.mm"
include "eeanv.mm"
include "sylibr.mm"
include "2eximi.mm"
include "syl.mm"
include "biimprcd.mm"
include "ancld.mm"
include "2eximdv.mm"
include "syl5com.mm"
include "impbid2.mm"

theorem cgsex2g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume cgsex2g.1: |- ( ( x = A /\ y = B ) -> ch )
  assume cgsex2g.2: |- ( ch -> ( ph <-> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. V /\ B e. W ) -> ( E. x E. y ( ch /\ ph ) <-> ps ) )

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
    wch
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    wps
    @3
    wps
    vx
    vy
    wch
    wph
    wps
    cgsex2g.2
    biimpa
    exlimivv
    @2
    wch
    vy
    wex
    vx
    wex
    #
    wps
    @4
    @2
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
    @5
    @2
    @6
    vx
    wex
    #
    @7
    vy
    wex
    #
    wa
    @9
    @0
    @10
    @1
    @11
    vx
    cA
    cV
    elisset
    vy
    cB
    cW
    elisset
    anim12i
    @6
    @7
    vx
    vy
    eeanv
    sylibr
    @8
    wch
    vx
    vy
    cgsex2g.1
    2eximi
    syl
    wps
    wch
    @3
    vx
    vy
    wps
    wch
    wph
    wch
    wph
    wps
    cgsex2g.2
    biimprcd
    ancld
    2eximdv
    syl5com
    impbid2
end
