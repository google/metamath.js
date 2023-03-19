include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "elisset.mm"
include "anim12i.mm"
include "eeanv.mm"
include "sylibr.mm"
include "nfv.mm"
include "nfan.mm"
include "anass.mm"
include "ancom.mm"
include "anbi1i.mm"
include "bitr3i.mm"
include "biimparc.mm"
include "sylbir.mm"
include "ex.mm"
include "eximd.mm"
include "impancom.mm"
include "sylan2.mm"

theorem spc2ed
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume spc2ed.x: |- F/ x ch
  assume spc2ed.y: |- F/ y ch
  assume spc2ed.1: |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ( ph /\ ( A e. V /\ B e. W ) ) -> ( ch -> E. x E. y ps ) )

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
    wph
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
    #
    vx
    wex
    #
    wch
    wps
    vy
    wex
    #
    vx
    wex
    #
    wi
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
    @7
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
    @3
    @4
    vx
    vy
    eeanv
    sylibr
    wph
    wch
    @7
    @9
    wph
    wch
    wa
    #
    @6
    @8
    vx
    wph
    wch
    vx
    wph
    vx
    nfv
    spc2ed.x
    nfan
    @12
    @5
    wps
    vy
    wph
    wch
    vy
    wph
    vy
    nfv
    spc2ed.y
    nfan
    @12
    @5
    wps
    @12
    @5
    wa
    #
    wch
    wph
    @5
    wa
    #
    wa
    #
    wps
    @15
    wch
    wph
    wa
    #
    @5
    wa
    @13
    wch
    wph
    @5
    anass
    @16
    @12
    @5
    wch
    wph
    ancom
    anbi1i
    bitr3i
    @14
    wps
    wch
    spc2ed.1
    biimparc
    sylbir
    ex
    eximd
    eximd
    impancom
    sylan2
end
