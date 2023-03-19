include "wcel.mm"
include "w3a.mm"
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
include "wb.mm"
include "wi.mm"
include "eqeq2.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "copab.mm"
include "wfn.mm"
include "weu.mm"
include "wal.mm"
include "ex.mm"
include "alrimivv.mm"
include "fnoprabg.mm"
include "syl.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "opelopabg.mm"
include "ibir.mm"
include "fnopfvb.mm"
include "syl2an.mm"
include "vtoclg.mm"
include "com12.mm"
include "exp32.mm"
include "3imp2.mm"
include "anbi12d.mm"
include "eloprabg.mm"
include "adantl.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "biidd.mm"
include "bianabs.mm"
include "3adant3.mm"

theorem ovg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let vc: setvar c
  assume ovg.1: |- ( x = A -> ( ph <-> ps ) )
  assume ovg.2: |- ( y = B -> ( ps <-> ch ) )
  assume ovg.3: |- ( z = C -> ( ch <-> th ) )
  assume ovg.4: |- ( ( ta /\ ( x e. R /\ y e. S ) ) -> E! z ph )
  assume ovg.5: |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) }

  disjoint ps x
  disjoint ch x
  disjoint ch y
  disjoint x y
  disjoint th x
  disjoint th y
  disjoint th z
  disjoint x z
  disjoint y z
  disjoint ta x
  disjoint ta y
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint c ph
  disjoint c ta
  disjoint c x
  disjoint c y
  disjoint R c
  disjoint c z
  disjoint S c
  disjoint A c
  disjoint B c
  disjoint C c
  assert |- ( ( ta /\ ( A e. R /\ B e. S /\ C e. D ) ) -> ( ( A F B ) = C <-> th ) )

  proof
    wta
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cD
    wcel
    #
    w3a
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
    @0
    @1
    wa
    #
    wth
    wa
    #
    wth
    @6
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
    @4
    @8
    @5
    @17
    cC
    @5
    @9
    cF
    cfv
    @17
    cA
    cB
    cF
    df-ov
    @9
    cF
    @16
    ovg.5
    fveq1i
    eqtri
    eqeq1i
    @4
    @18
    @9
    cC
    cop
    #
    @16
    wcel
    #
    @8
    wta
    @0
    @1
    @2
    @18
    @20
    wb
    #
    wta
    @0
    @1
    @2
    @21
    wi
    @2
    wta
    @7
    wa
    #
    @21
    @22
    @17
    vc
    cv
    #
    wceq
    #
    @9
    @23
    cop
    #
    @16
    wcel
    #
    wb
    #
    wi
    @22
    @21
    wi
    vc
    cC
    cD
    @23
    cC
    wceq
    #
    @27
    @21
    @22
    @28
    @24
    @18
    @26
    @20
    @23
    cC
    @17
    eqeq2
    @28
    @25
    @19
    @16
    @23
    cC
    @9
    opeq2
    eleq1d
    bibi12d
    imbi2d
    wta
    @16
    @14
    vx
    vy
    copab
    #
    wfn
    #
    @9
    @29
    wcel
    #
    @27
    @7
    wta
    @14
    wph
    vz
    weu
    #
    wi
    #
    vy
    wal
    vx
    wal
    @30
    wta
    @33
    vx
    vy
    wta
    @14
    @32
    ovg.4
    ex
    alrimivv
    @14
    wph
    vx
    vy
    vz
    fnoprabg
    syl
    @7
    @31
    @14
    @0
    @13
    wa
    #
    @7
    vx
    vy
    cA
    cB
    cR
    cS
    @10
    cA
    wceq
    #
    @11
    @0
    @13
    @10
    cA
    cR
    eleq1
    anbi1d
    #
    @12
    cB
    wceq
    #
    @13
    @1
    @0
    @12
    cB
    cS
    eleq1
    anbi2d
    #
    opelopabg
    ibir
    @29
    @9
    @23
    @16
    fnopfvb
    syl2an
    vtoclg
    com12
    exp32
    3imp2
    @3
    @20
    @8
    wb
    wta
    @15
    @34
    wps
    wa
    @7
    wch
    wa
    @8
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    cS
    cD
    @35
    @14
    @34
    wph
    wps
    @36
    ovg.1
    anbi12d
    @37
    @34
    @7
    wps
    wch
    @38
    ovg.2
    anbi12d
    vz
    cv
    cC
    wceq
    wch
    wth
    @7
    ovg.3
    anbi2d
    eloprabg
    adantl
    bitrd
    syl5bb
    @3
    @8
    wth
    wb
    #
    wta
    @0
    @1
    @39
    @2
    @7
    @8
    wth
    @7
    @8
    biidd
    bianabs
    3adant3
    adantl
    bitrd
end
