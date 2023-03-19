include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wiso.mm"
include "wcel.mm"
include "wn.mm"
include "cxp.mm"
include "brxp.mm"
include "cdif.mm"
include "breqi.mm"
include "brdif.mm"
include "bitri.mm"
include "baib.mm"
include "sylbir.mm"
include "adantl.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "sylibr.mm"
include "sylan.mm"
include "syl.mm"
include "bibi12d.mm"
include "notbi.mm"
include "syl6rbbr.mm"
include "2ralbidva.mm"
include "pm5.32i.mm"
include "df-isom.mm"
include "3bitr4i.mm"

theorem isocnv3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isocnv3.1: |- C = ( ( A X. A ) \ R )
  assume isocnv3.2: |- D = ( ( B X. B ) \ S )


  assert |- ( H Isom R , S ( A , B ) <-> H Isom C , D ( A , B ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    cH
    cfv
    #
    @2
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @0
    @1
    @2
    cC
    wbr
    #
    @4
    @5
    cD
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cB
    cC
    cD
    cH
    wiso
    @0
    @8
    @12
    @0
    @7
    @11
    vx
    vy
    cA
    cA
    @0
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    #
    wa
    #
    @11
    @3
    wn
    #
    @6
    wn
    #
    wb
    @7
    @16
    @9
    @17
    @10
    @18
    @15
    @9
    @17
    wb
    #
    @0
    @15
    @1
    @2
    cA
    cA
    cxp
    #
    wbr
    #
    @19
    @1
    @2
    cA
    cA
    brxp
    @9
    @21
    @17
    @9
    @1
    @2
    @20
    cR
    cdif
    #
    wbr
    @21
    @17
    wa
    @1
    @2
    cC
    @22
    isocnv3.1
    breqi
    @1
    @2
    @20
    cR
    brdif
    bitri
    baib
    sylbir
    adantl
    @16
    @4
    @5
    cB
    cB
    cxp
    #
    wbr
    #
    @10
    @18
    wb
    @0
    cA
    cB
    cH
    wf
    #
    @15
    @24
    cA
    cB
    cH
    f1of
    @25
    @15
    wa
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    @24
    @25
    @13
    @26
    @14
    @27
    cA
    cB
    @1
    cH
    ffvelrn
    cA
    cB
    @2
    cH
    ffvelrn
    anim12dan
    @4
    @5
    cB
    cB
    brxp
    sylibr
    sylan
    @10
    @24
    @18
    @10
    @4
    @5
    @23
    cS
    cdif
    #
    wbr
    @24
    @18
    wa
    @4
    @5
    cD
    @28
    isocnv3.2
    breqi
    @4
    @5
    @23
    cS
    brdif
    bitri
    baib
    syl
    bibi12d
    @3
    @6
    notbi
    syl6rbbr
    2ralbidva
    pm5.32i
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    vx
    vy
    cA
    cB
    cC
    cD
    cH
    df-isom
    3bitr4i
end
