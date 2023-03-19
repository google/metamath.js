include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cop.mm"
include "cv.mm"
include "coprab.mm"
include "cfv.mm"
include "df-ov.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "copab.mm"
include "wfn.mm"
include "wb.mm"
include "fnoprab.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "opelopabg.mm"
include "ibir.mm"
include "fnopfvb.mm"
include "sylancr.mm"
include "cvv.mm"
include "anbi12d.mm"
include "eloprabg.mm"
include "mp3an3.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "bianabs.mm"

theorem ov
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume ov.1: |- C e. _V
  assume ov.2: |- ( x = A -> ( ph <-> ps ) )
  assume ov.3: |- ( y = B -> ( ps <-> ch ) )
  assume ov.4: |- ( z = C -> ( ch <-> th ) )
  assume ov.5: |- ( ( x e. R /\ y e. S ) -> E! z ph )
  assume ov.6: |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) }

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint th x
  disjoint th y
  disjoint th z
  assert |- ( ( A e. R /\ B e. S ) -> ( ( A F B ) = C <-> th ) )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    cA
    cB
    cF
    co
    #
    cC
    wceq
    #
    wth
    @4
    cA
    cB
    cop
    #
    vx
    cv
    #
    cR
    wcel
    #
    vy
    cv
    #
    cS
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
    #
    cfv
    #
    cC
    wceq
    #
    @2
    @2
    wth
    wa
    #
    @3
    @13
    cC
    @3
    @5
    cF
    cfv
    @13
    cA
    cB
    cF
    df-ov
    @5
    cF
    @12
    ov.6
    fveq1i
    eqtri
    eqeq1i
    @2
    @14
    @5
    cC
    cop
    @12
    wcel
    #
    @15
    @2
    @12
    @10
    vx
    vy
    copab
    #
    wfn
    @5
    @17
    wcel
    #
    @14
    @16
    wb
    @10
    wph
    vx
    vy
    vz
    ov.5
    fnoprab
    @2
    @18
    @10
    @0
    @9
    wa
    #
    @2
    vx
    vy
    cA
    cB
    cR
    cS
    @6
    cA
    wceq
    #
    @7
    @0
    @9
    @6
    cA
    cR
    eleq1
    anbi1d
    #
    @8
    cB
    wceq
    #
    @9
    @1
    @0
    @8
    cB
    cS
    eleq1
    anbi2d
    #
    opelopabg
    ibir
    @17
    @5
    cC
    @12
    fnopfvb
    sylancr
    @0
    @1
    cC
    cvv
    wcel
    @16
    @15
    wb
    ov.1
    @11
    @19
    wps
    wa
    @2
    wch
    wa
    @15
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    cS
    cvv
    @20
    @10
    @19
    wph
    wps
    @21
    ov.2
    anbi12d
    @22
    @19
    @2
    wps
    wch
    @23
    ov.3
    anbi12d
    vz
    cv
    cC
    wceq
    wch
    wth
    @2
    ov.4
    anbi2d
    eloprabg
    mp3an3
    bitrd
    syl5bb
    bianabs
end
