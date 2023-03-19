include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "wrex.mm"
include "wel.mm"
include "wo.mm"
include "dfdif2.mm"
include "cun.mm"
include "dfnul3.mm"
include "uneq2i.mm"
include "un0.mm"
include "unrab.mm"
include "3eqtr3i.mm"
include "wa.mm"
include "ianor.mm"
include "wex.mm"
include "eluni.mm"
include "anbi1i.mm"
include "df-rex.mm"
include "elin.mm"
include "anbi2i.mm"
include "df-an.mm"
include "bitr3i.mm"
include "eldifsn.mm"
include "necom.mm"
include "bitri.mm"
include "ancom.mm"
include "anbi2ci.mm"
include "anass.mm"
include "3bitri.mm"
include "an32.mm"
include "exbii.mm"
include "19.41v.mm"
include "rexnal.mm"
include "3bitr2ri.mm"
include "con1bii.mm"
include "rabbii.mm"
include "3eqtri.mm"
include "neeq1i.mm"
include "rabn0.mm"

theorem kmlem3
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let vu: setvar u
  let vy: setvar y
  let wph: wff ph
  let wps: wff ps

  disjoint v x
  disjoint v w
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v y
  disjoint ph v
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps v
  disjoint u w
  disjoint u z
  disjoint w y
  disjoint y z
  assert |- ( ( z \ U. ( x \ { z } ) ) =/= (/) <-> E. v e. z A. w e. x ( z =/= w -> -. v e. ( z i^i w ) ) )

  proof
    vz
    cv
    #
    vx
    cv
    #
    @0
    csn
    cdif
    #
    cuni
    #
    cdif
    #
    c0
    wne
    @0
    vw
    cv
    #
    wne
    #
    vv
    cv
    #
    @0
    @5
    cin
    wcel
    #
    wn
    wi
    #
    vw
    @1
    wral
    #
    vv
    @0
    crab
    #
    c0
    wne
    @10
    vv
    @0
    wrex
    @4
    @11
    c0
    @4
    @7
    @3
    wcel
    #
    wn
    #
    vv
    @0
    crab
    #
    @13
    vv
    vz
    wel
    #
    wn
    #
    wo
    #
    vv
    @0
    crab
    #
    @11
    vv
    @0
    @3
    dfdif2
    @14
    c0
    cun
    @14
    @16
    vv
    @0
    crab
    #
    cun
    @14
    @18
    c0
    @19
    @14
    vv
    @0
    dfnul3
    uneq2i
    @14
    un0
    @13
    @16
    vv
    @0
    unrab
    3eqtr3i
    @17
    @10
    vv
    @0
    @17
    @12
    @15
    wa
    #
    wn
    @10
    @12
    @15
    ianor
    @10
    @20
    @20
    vv
    vw
    wel
    #
    @5
    @2
    wcel
    #
    wa
    #
    vw
    wex
    #
    @15
    wa
    #
    @9
    wn
    #
    vw
    @1
    wrex
    #
    @10
    wn
    @12
    @24
    @15
    vw
    @7
    @2
    eluni
    anbi1i
    @27
    vw
    vx
    wel
    #
    @26
    wa
    #
    vw
    wex
    @23
    @15
    wa
    #
    vw
    wex
    @25
    @26
    vw
    @1
    df-rex
    @29
    @30
    vw
    @29
    @28
    @6
    @15
    @21
    wa
    #
    wa
    #
    wa
    #
    @30
    @32
    @26
    @28
    @32
    @6
    @8
    wa
    @26
    @8
    @31
    @6
    @7
    @0
    @5
    elin
    anbi2i
    @6
    @8
    df-an
    bitr3i
    anbi2i
    @33
    @21
    @15
    wa
    #
    @22
    wa
    #
    @30
    @35
    @34
    @28
    @6
    wa
    #
    wa
    @36
    @31
    wa
    @33
    @22
    @36
    @34
    @22
    @28
    @5
    @0
    wne
    #
    wa
    @36
    @5
    @1
    @0
    eldifsn
    @37
    @6
    @28
    @5
    @0
    necom
    anbi2i
    bitri
    anbi2i
    @34
    @31
    @36
    @21
    @15
    ancom
    anbi2ci
    @28
    @6
    @31
    anass
    3bitri
    @21
    @15
    @22
    an32
    bitr3i
    bitr3i
    exbii
    @23
    @15
    vw
    19.41v
    3bitri
    @9
    vw
    @1
    rexnal
    3bitr2ri
    con1bii
    bitr3i
    rabbii
    3eqtri
    neeq1i
    @10
    vv
    @0
    rabn0
    bitri
end
