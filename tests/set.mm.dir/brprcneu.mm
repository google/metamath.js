include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wmo.mm"
include "wi.mm"
include "weu.mm"
include "wa.mm"
include "weq.mm"
include "cop.mm"
include "c0.mm"
include "wal.mm"
include "dtru.mm"
include "exnal.mm"
include "equcom.mm"
include "albii.mm"
include "xchbinx.mm"
include "mpbir.mm"
include "jctr.mm"
include "19.42v.mm"
include "sylibr.mm"
include "opprc1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "anidm.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "df-br.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "exbii.mm"
include "3imtr4g.mm"
include "eximdv.mm"
include "exanali.mm"
include "breq2.mm"
include "mo4.mm"
include "notbii.mm"
include "3bitr4ri.mm"
include "syl6ibr.mm"
include "eu5.mm"
include "imnan.mm"
include "bitr4i.mm"

theorem brprcneu
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint F y
  assert |- ( -. A e. _V -> -. E! x A F x )

  proof
    cA
    cvv
    wcel
    wn
    #
    cA
    vx
    cv
    #
    cF
    wbr
    #
    vx
    wex
    #
    @2
    vx
    wmo
    #
    wn
    #
    wi
    #
    @2
    vx
    weu
    #
    wn
    #
    @0
    @3
    @2
    cA
    vy
    cv
    #
    cF
    wbr
    #
    wa
    #
    vx
    vy
    weq
    #
    wn
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @5
    @0
    @2
    @15
    vx
    @0
    cA
    @1
    cop
    #
    cF
    wcel
    #
    @18
    cA
    @9
    cop
    #
    cF
    wcel
    #
    wa
    #
    @13
    wa
    #
    vy
    wex
    #
    @2
    @15
    @0
    @18
    @23
    wi
    c0
    cF
    wcel
    #
    @24
    @13
    wa
    #
    vy
    wex
    #
    wi
    @24
    @24
    @13
    vy
    wex
    #
    wa
    @26
    @24
    @27
    @27
    vy
    vx
    weq
    #
    vy
    wal
    #
    wn
    vy
    vx
    dtru
    @27
    @12
    vy
    wal
    @29
    @12
    vy
    exnal
    @12
    @28
    vy
    vx
    vy
    equcom
    albii
    xchbinx
    mpbir
    jctr
    @24
    @13
    vy
    19.42v
    sylibr
    @0
    @18
    @24
    @23
    @26
    @0
    @17
    c0
    cF
    cA
    @1
    opprc1
    eleq1d
    #
    @0
    @22
    @25
    vy
    @0
    @21
    @24
    @13
    @0
    @21
    @24
    @24
    wa
    @24
    @0
    @18
    @24
    @20
    @24
    @30
    @0
    @19
    c0
    cF
    cA
    @9
    opprc1
    eleq1d
    anbi12d
    @24
    anidm
    syl6bb
    anbi1d
    exbidv
    imbi12d
    mpbiri
    cA
    @1
    cF
    df-br
    #
    @14
    @22
    vy
    @11
    @21
    @13
    @2
    @18
    @10
    @20
    @31
    cA
    @9
    cF
    df-br
    anbi12i
    anbi1i
    exbii
    3imtr4g
    eximdv
    @11
    @12
    wi
    vy
    wal
    #
    wn
    #
    vx
    wex
    @32
    vx
    wal
    #
    wn
    @16
    @5
    @32
    vx
    exnal
    @15
    @33
    vx
    @11
    @12
    vy
    exanali
    exbii
    @4
    @34
    @2
    @10
    vx
    vy
    @1
    @9
    cA
    cF
    breq2
    mo4
    notbii
    3bitr4ri
    syl6ibr
    @8
    @3
    @4
    wa
    #
    wn
    @6
    @7
    @35
    @2
    vx
    eu5
    notbii
    @3
    @4
    imnan
    bitr4i
    sylibr
end
