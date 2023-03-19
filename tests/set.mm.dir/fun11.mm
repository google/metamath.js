include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "ccnv.mm"
include "wfun.mm"
include "dfbi2.mm"
include "imbi2i.mm"
include "pm4.76.mm"
include "bi2.04.mm"
include "anbi12i.mm"
include "3bitr2i.mm"
include "2albii.mm"
include "19.26-2.mm"
include "alcom.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "equsalvw.mm"
include "albii.mm"
include "bitri.mm"
include "breq2.mm"
include "3bitri.mm"
include "bitr2i.mm"
include "wmo.mm"
include "fun2cnv.mm"
include "mo4.mm"
include "funcnv2.mm"
include "alrot4.mm"
include "3bitr4i.mm"

theorem fun11
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( ( Fun `' `' A /\ Fun `' A ) <-> A. x A. y A. z A. w ( ( x A y /\ z A w ) -> ( x = z <-> y = w ) ) )

  proof
    vz
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    @0
    vw
    cv
    #
    cA
    wbr
    #
    wa
    #
    vy
    vw
    weq
    #
    wi
    #
    vy
    wal
    #
    vw
    wal
    #
    vz
    wal
    #
    vx
    cv
    #
    @3
    cA
    wbr
    #
    @4
    wa
    #
    vx
    vz
    weq
    #
    wi
    #
    vx
    wal
    #
    vw
    wal
    vz
    wal
    #
    wa
    #
    @11
    @1
    cA
    wbr
    #
    @4
    wa
    #
    @14
    @6
    wb
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    vw
    wal
    vz
    wal
    #
    cA
    ccnv
    #
    ccnv
    wfun
    #
    @25
    wfun
    #
    wa
    @22
    vw
    wal
    vz
    wal
    vy
    wal
    vx
    wal
    @24
    @8
    @16
    wa
    #
    vw
    wal
    vz
    wal
    @18
    @23
    @28
    vz
    vw
    @23
    @14
    @20
    @6
    wi
    #
    wi
    #
    @6
    @20
    @14
    wi
    #
    wi
    #
    wa
    #
    vy
    wal
    vx
    wal
    @30
    vy
    wal
    vx
    wal
    #
    @32
    vy
    wal
    #
    vx
    wal
    #
    wa
    @28
    @22
    @33
    vx
    vy
    @22
    @20
    @14
    @6
    wi
    #
    @6
    @14
    wi
    #
    wa
    #
    wi
    @20
    @37
    wi
    #
    @20
    @38
    wi
    #
    wa
    @33
    @21
    @39
    @20
    @14
    @6
    dfbi2
    imbi2i
    @20
    @37
    @38
    pm4.76
    @40
    @30
    @41
    @32
    @20
    @14
    @6
    bi2.04
    @20
    @6
    @14
    bi2.04
    anbi12i
    3bitr2i
    2albii
    @30
    @32
    vx
    vy
    19.26-2
    @34
    @8
    @36
    @16
    @34
    @30
    vx
    wal
    #
    vy
    wal
    @8
    @30
    vx
    vy
    alcom
    @42
    @7
    vy
    @29
    @7
    vx
    vz
    @14
    @20
    @5
    @6
    @14
    @19
    @2
    @4
    @11
    @0
    @1
    cA
    breq1
    anbi1d
    imbi1d
    equsalvw
    albii
    bitri
    @35
    @15
    vx
    @31
    @15
    vy
    vw
    @6
    @20
    @13
    @14
    @6
    @19
    @12
    @4
    @1
    @3
    @11
    cA
    breq2
    anbi1d
    imbi1d
    equsalvw
    albii
    anbi12i
    3bitri
    2albii
    @8
    @16
    vz
    vw
    19.26-2
    bitr2i
    @26
    @10
    @27
    @17
    @26
    @2
    vy
    wmo
    #
    vz
    wal
    @7
    vw
    wal
    vy
    wal
    #
    vz
    wal
    @10
    vz
    vy
    cA
    fun2cnv
    @43
    @44
    vz
    @2
    @4
    vy
    vw
    @1
    @3
    @0
    cA
    breq2
    mo4
    albii
    @44
    @9
    vz
    @7
    vy
    vw
    alcom
    albii
    3bitri
    @27
    @12
    vx
    wmo
    #
    vw
    wal
    @15
    vz
    wal
    vx
    wal
    #
    vw
    wal
    #
    @17
    vx
    vw
    cA
    funcnv2
    @45
    @46
    vw
    @12
    @4
    vx
    vz
    @11
    @0
    @3
    cA
    breq1
    mo4
    albii
    @47
    @16
    vz
    wal
    #
    vw
    wal
    @17
    @46
    @48
    vw
    @15
    vx
    vz
    alcom
    albii
    @16
    vw
    vz
    alcom
    bitri
    3bitri
    anbi12i
    @22
    vx
    vy
    vz
    vw
    alrot4
    3bitr4i
end
