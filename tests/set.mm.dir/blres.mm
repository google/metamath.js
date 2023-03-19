include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cin.mm"
include "cxr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "inss2.mm"
include "sseli.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "ovres.mm"
include "syl5eq.mm"
include "sylan.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "pm5.32da.mm"
include "3ad2ant2.mm"
include "elin.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitr4g.mm"
include "xmetres.mm"
include "syl5eqel.mm"
include "elbl.mm"
include "syl3an1.mm"
include "inss1.mm"
include "syl3an2.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem blres
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vb: setvar b
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  assume blres.2: |- C = ( D |` ( Y X. Y ) )


  assert |- ( ( D e. ( *Met ` X ) /\ P e. ( X i^i Y ) /\ R e. RR* ) -> ( P ( ball ` C ) R ) = ( ( P ( ball ` D ) R ) i^i Y ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    cY
    cin
    #
    wcel
    #
    cR
    cxr
    wcel
    #
    w3a
    #
    vx
    cP
    cR
    cC
    cbl
    cfv
    co
    #
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    cY
    cin
    #
    @4
    vx
    cv
    #
    @1
    wcel
    #
    cP
    @8
    cC
    co
    #
    cR
    clt
    wbr
    #
    wa
    #
    @8
    cX
    wcel
    #
    cP
    @8
    cD
    co
    #
    cR
    clt
    wbr
    #
    wa
    #
    @8
    cY
    wcel
    #
    wa
    #
    @8
    @5
    wcel
    #
    @8
    @7
    wcel
    #
    @4
    @17
    @13
    @11
    wa
    #
    wa
    #
    @17
    @16
    wa
    #
    @12
    @18
    @2
    @0
    @22
    @23
    wb
    @3
    @2
    @17
    @21
    @16
    @2
    @17
    wa
    #
    @11
    @15
    @13
    @24
    @10
    @14
    cR
    clt
    @2
    cP
    cY
    wcel
    #
    @17
    @10
    @14
    wceq
    @1
    cY
    cP
    cX
    cY
    inss2
    sseli
    @25
    @17
    wa
    @10
    cP
    @8
    cD
    cY
    cY
    cxp
    cres
    #
    co
    @14
    cC
    @26
    cP
    @8
    blres.2
    oveqi
    cP
    @8
    cY
    cY
    cD
    ovres
    syl5eq
    sylan
    breq1d
    anbi2d
    pm5.32da
    3ad2ant2
    @12
    @17
    @13
    wa
    #
    @11
    wa
    @22
    @9
    @27
    @11
    @9
    @13
    @17
    wa
    @27
    @8
    cX
    cY
    elin
    @13
    @17
    ancom
    bitri
    anbi1i
    @17
    @13
    @11
    anass
    bitri
    @16
    @17
    ancom
    3bitr4g
    @0
    cC
    @1
    cxmt
    cfv
    #
    wcel
    @2
    @3
    @19
    @12
    wb
    @0
    cC
    @26
    @28
    blres.2
    cD
    cY
    cX
    xmetres
    syl5eqel
    @8
    cC
    cP
    cR
    @1
    elbl
    syl3an1
    @20
    @8
    @6
    wcel
    #
    @17
    wa
    @4
    @18
    @8
    @6
    cY
    elin
    @4
    @29
    @16
    @17
    @2
    @0
    cP
    cX
    wcel
    @3
    @29
    @16
    wb
    @1
    cX
    cP
    cX
    cY
    inss1
    sseli
    @8
    cD
    cP
    cR
    cX
    elbl
    syl3an2
    anbi1d
    syl5bb
    3bitr4d
    eqrdv
end
