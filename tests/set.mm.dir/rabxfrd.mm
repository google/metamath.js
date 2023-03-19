include "wcel.mm"
include "crab.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "ex.mm"
include "ibibr.mm"
include "sylib.mm"
include "imp.mm"
include "anbi1d.mm"
include "elrab.mm"
include "rabid.mm"
include "3bitr4g.mm"
include "rabbidva.mm"
include "eleq2d.mm"
include "nfcv.mm"
include "nfel1.mm"
include "wceq.mm"
include "eleq1d.mm"
include "elrabf.mm"
include "nfrab1.mm"
include "nfel.mm"
include "eleq1.mm"
include "3bitr3g.mm"
include "pm5.32.mm"
include "sylibr.mm"

theorem rabxfrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rabxfrd.1: |- F/_ y B
  assume rabxfrd.2: |- F/_ y C
  assume rabxfrd.3: |- ( ( ph /\ y e. D ) -> A e. D )
  assume rabxfrd.4: |- ( x = A -> ( ps <-> ch ) )
  assume rabxfrd.5: |- ( y = B -> A = C )

  disjoint A x
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint ph y
  disjoint ps y
  disjoint ch x
  assert |- ( ( ph /\ B e. D ) -> ( C e. { x e. D | ps } <-> B e. { y e. D | ch } ) )

  proof
    wph
    cB
    cD
    wcel
    #
    cC
    wps
    vx
    cD
    crab
    #
    wcel
    #
    cB
    wch
    vy
    cD
    crab
    #
    wcel
    #
    wb
    #
    wph
    @0
    @2
    wa
    #
    @0
    @4
    wa
    #
    wb
    @0
    @5
    wi
    wph
    cB
    cA
    @1
    wcel
    #
    vy
    cD
    crab
    #
    wcel
    cB
    vy
    cv
    #
    @3
    wcel
    #
    vy
    cD
    crab
    #
    wcel
    @6
    @7
    wph
    @9
    @12
    cB
    wph
    @8
    @11
    vy
    cD
    wph
    @10
    cD
    wcel
    #
    wa
    #
    cA
    cD
    wcel
    #
    wch
    wa
    @13
    wch
    wa
    @8
    @11
    @14
    @15
    @13
    wch
    wph
    @13
    @15
    @13
    wb
    #
    wph
    @13
    @15
    wi
    @13
    @16
    wi
    wph
    @13
    @15
    rabxfrd.3
    ex
    @13
    @15
    ibibr
    sylib
    imp
    anbi1d
    wps
    wch
    vx
    cA
    cD
    rabxfrd.4
    elrab
    wch
    vy
    cD
    rabid
    3bitr4g
    rabbidva
    eleq2d
    @8
    @2
    vy
    cB
    cD
    rabxfrd.1
    vy
    cD
    nfcv
    #
    vy
    cC
    @1
    rabxfrd.2
    nfel1
    @10
    cB
    wceq
    cA
    cC
    @1
    rabxfrd.5
    eleq1d
    elrabf
    @11
    @4
    vy
    cB
    cD
    rabxfrd.1
    @17
    vy
    cB
    @3
    rabxfrd.1
    wch
    vy
    cD
    nfrab1
    nfel
    @10
    cB
    @3
    eleq1
    elrabf
    3bitr3g
    @0
    @2
    @4
    pm5.32
    sylibr
    imp
end
