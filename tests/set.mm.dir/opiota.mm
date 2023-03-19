include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "weu.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "w3a.mm"
include "ceqsrex2v.mm"
include "bicomd.mm"
include "cio.mm"
include "cvv.mm"
include "opex.mm"
include "a1i.mm"
include "id.mm"
include "wb.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "vex.mm"
include "opth.mm"
include "bitri.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "adantl.mm"
include "nfeu1.mm"
include "nfvd.mm"
include "nfcvd.mm"
include "iota2df.mm"
include "eqeq1i.mm"
include "syl6bbr.mm"
include "sylan9bbr.mm"
include "pm5.32da.mm"
include "cxp.mm"
include "cab.mm"
include "opelxpi.mm"
include "simpl.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "abssi.mm"
include "iotacl.mm"
include "sseldi.mm"
include "syl5eqel.mm"
include "opelxp.mm"
include "eleq1.mm"
include "syl5bbr.mm"
include "pm4.71rd.mm"
include "1st2nd2.mm"
include "syl.mm"
include "eqeq2d.mm"
include "3bitr2d.mm"
include "df-3an.mm"
include "eqeq2i.mm"
include "anbi12i.mm"
include "fvex.mm"
include "opth2.mm"
include "bitr4i.mm"
include "3bitr4g.mm"

theorem opiota
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cI: class I
  let cX: class X
  let cY: class Y
  assume opiota.1: |- I = ( iota z E. x e. A E. y e. B ( z = <. x , y >. /\ ph ) )
  assume opiota.2: |- X = ( 1st ` I )
  assume opiota.3: |- Y = ( 2nd ` I )
  assume opiota.4: |- ( x = C -> ( ph <-> ps ) )
  assume opiota.5: |- ( y = D -> ( ps <-> ch ) )

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
  disjoint ch y
  disjoint ph z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ps x
  assert |- ( E! z E. x e. A E. y e. B ( z = <. x , y >. /\ ph ) -> ( ( C e. A /\ D e. B /\ ch ) <-> ( C = X /\ D = Y ) ) )

  proof
    vz
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
    cB
    wrex
    vx
    cA
    wrex
    #
    vz
    weu
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    wa
    #
    wch
    wa
    #
    cC
    cD
    cop
    #
    cI
    c1st
    cfv
    #
    cI
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @8
    @9
    wch
    w3a
    cC
    cX
    wceq
    #
    cD
    cY
    wceq
    #
    wa
    #
    @7
    @11
    @10
    @12
    cI
    wceq
    #
    wa
    @20
    @16
    @7
    @10
    wch
    @20
    @10
    wch
    @1
    cC
    wceq
    @2
    cD
    wceq
    wa
    #
    wph
    wa
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @7
    @20
    @10
    @23
    wch
    wph
    wps
    wch
    vx
    vy
    cC
    cD
    cA
    cB
    opiota.4
    opiota.5
    ceqsrex2v
    bicomd
    @7
    @23
    @6
    vz
    cio
    #
    @12
    wceq
    #
    @20
    @7
    @6
    @23
    vz
    @12
    cvv
    @12
    cvv
    wcel
    @7
    cC
    cD
    opex
    a1i
    @7
    id
    @0
    @12
    wceq
    #
    @6
    @23
    wb
    @7
    @26
    @5
    @22
    vx
    vy
    cA
    cB
    @26
    @4
    @21
    wph
    @26
    @4
    @12
    @3
    wceq
    #
    @21
    @0
    @12
    @3
    eqeq1
    @27
    @3
    @12
    wceq
    @21
    @12
    @3
    eqcom
    @1
    @2
    cC
    cD
    vx
    vex
    vy
    vex
    opth
    bitri
    syl6bb
    anbi1d
    2rexbidv
    adantl
    @6
    vz
    nfeu1
    @7
    @23
    vz
    nfvd
    @7
    vz
    @12
    nfcvd
    iota2df
    @20
    cI
    @12
    wceq
    @25
    @12
    cI
    eqcom
    cI
    @24
    @12
    opiota.1
    eqeq1i
    bitri
    syl6bbr
    sylan9bbr
    pm5.32da
    @7
    @20
    @10
    @7
    @10
    @20
    cI
    cA
    cB
    cxp
    #
    wcel
    #
    @7
    cI
    @24
    @28
    opiota.1
    @7
    @6
    vz
    cab
    @28
    @24
    @6
    vz
    @28
    @5
    @0
    @28
    wcel
    #
    vx
    vy
    cA
    cB
    @1
    cA
    wcel
    @2
    cB
    wcel
    wa
    @30
    @5
    @3
    @28
    wcel
    @1
    @2
    cA
    cB
    opelxpi
    @5
    @0
    @3
    @28
    @4
    wph
    simpl
    eleq1d
    syl5ibrcom
    rexlimivv
    abssi
    @6
    vz
    iotacl
    sseldi
    syl5eqel
    #
    @10
    @12
    @28
    wcel
    @20
    @29
    cC
    cD
    cA
    cB
    opelxp
    @12
    cI
    @28
    eleq1
    syl5bbr
    syl5ibrcom
    pm4.71rd
    @7
    cI
    @15
    @12
    @7
    @29
    cI
    @15
    wceq
    @31
    cI
    cA
    cB
    1st2nd2
    syl
    eqeq2d
    3bitr2d
    @8
    @9
    wch
    df-3an
    @19
    cC
    @13
    wceq
    #
    cD
    @14
    wceq
    #
    wa
    @16
    @17
    @32
    @18
    @33
    cX
    @13
    cC
    opiota.2
    eqeq2i
    cY
    @14
    cD
    opiota.3
    eqeq2i
    anbi12i
    cC
    cD
    @13
    @14
    cI
    c1st
    fvex
    cI
    c2nd
    fvex
    opth2
    bitr4i
    3bitr4g
end
