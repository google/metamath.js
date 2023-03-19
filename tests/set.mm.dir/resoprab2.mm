include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "coprab.mm"
include "cxp.mm"
include "cres.mm"
include "resoprab.mm"
include "anass.mm"
include "an4.mm"
include "ssel.mm"
include "pm4.71d.mm"
include "bicomd.mm"
include "bi2anan9.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "syl5bbr.mm"
include "oprabbidv.mm"
include "syl5eq.mm"

theorem resoprab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E z
  assert |- ( ( C C_ A /\ D C_ B ) -> ( { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } |` ( C X. D ) ) = { <. <. x , y >. , z >. | ( ( x e. C /\ y e. D ) /\ ph ) } )

  proof
    cC
    cA
    wss
    #
    cD
    cB
    wss
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wph
    wa
    #
    vx
    vy
    vz
    coprab
    cC
    cD
    cxp
    cres
    @3
    cC
    wcel
    #
    @5
    cD
    wcel
    #
    wa
    #
    @8
    wa
    #
    vx
    vy
    vz
    coprab
    @11
    wph
    wa
    #
    vx
    vy
    vz
    coprab
    @8
    vx
    vy
    vz
    cC
    cD
    resoprab
    @2
    @12
    @13
    vx
    vy
    vz
    @12
    @11
    @7
    wa
    #
    wph
    wa
    @2
    @13
    @11
    @7
    wph
    anass
    @2
    @14
    @11
    wph
    @14
    @9
    @4
    wa
    #
    @10
    @6
    wa
    #
    wa
    @2
    @11
    @9
    @10
    @4
    @6
    an4
    @0
    @15
    @9
    @1
    @16
    @10
    @0
    @9
    @15
    @0
    @9
    @4
    cC
    cA
    @3
    ssel
    pm4.71d
    bicomd
    @1
    @10
    @16
    @1
    @10
    @6
    cD
    cB
    @5
    ssel
    pm4.71d
    bicomd
    bi2anan9
    syl5bb
    anbi1d
    syl5bbr
    oprabbidv
    syl5eq
end
