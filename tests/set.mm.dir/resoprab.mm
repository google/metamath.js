include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cxp.mm"
include "cres.mm"
include "wcel.mm"
include "coprab.mm"
include "resopab.mm"
include "19.42vv.mm"
include "an12.mm"
include "eleq1.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "2exbii.mm"
include "bitr3i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "dfoprab2.mm"
include "reseq1i.mm"
include "3eqtr4i.mm"

theorem resoprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint ph w
  assert |- ( { <. <. x , y >. , z >. | ph } |` ( A X. B ) ) = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) }

  proof
    vw
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    copab
    #
    cA
    cB
    cxp
    #
    cres
    #
    @4
    @1
    cA
    wcel
    @2
    cB
    wcel
    wa
    #
    wph
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    copab
    #
    wph
    vx
    vy
    vz
    coprab
    #
    @8
    cres
    @11
    vx
    vy
    vz
    coprab
    @9
    @0
    @8
    wcel
    #
    @6
    wa
    #
    vw
    vz
    copab
    @14
    @6
    vw
    vz
    @8
    resopab
    @17
    @13
    vw
    vz
    @17
    @16
    @5
    wa
    #
    vy
    wex
    vx
    wex
    @13
    @16
    @5
    vx
    vy
    19.42vv
    @18
    @12
    vx
    vy
    @18
    @4
    @16
    wph
    wa
    #
    wa
    @12
    @16
    @4
    wph
    an12
    @4
    @19
    @11
    @4
    @16
    @10
    wph
    @4
    @16
    @3
    @8
    wcel
    @10
    @0
    @3
    @8
    eleq1
    @1
    @2
    cA
    cB
    opelxp
    syl6bb
    anbi1d
    pm5.32i
    bitri
    2exbii
    bitr3i
    opabbii
    eqtri
    @15
    @7
    @8
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    reseq1i
    @11
    vx
    vy
    vz
    vw
    dfoprab2
    3eqtr4i
end
