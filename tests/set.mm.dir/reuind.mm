include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "wreu.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "r19.41v.mm"
include "exbii.mm"
include "rexcom4.mm"
include "risset.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"
include "bitri.mm"
include "wb.mm"
include "eqeq2.mm"
include "imim2i.mm"
include "biimpr.mm"
include "an31.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitr3i.mm"
include "sylib.mm"
include "syl.mm"
include "2alimi.mm"
include "19.23v.mm"
include "an12.mm"
include "eleq1.mm"
include "adantr.mm"
include "pm5.32ri.mm"
include "bitr4i.mm"
include "19.42v.mm"
include "albii.mm"
include "19.21v.mm"
include "expd.mm"
include "reximdvai.mm"
include "syl5bi.mm"
include "imp.mm"
include "pm4.24.mm"
include "biimpi.mm"
include "prth.mm"
include "eqtr3.mm"
include "syl56.mm"
include "alanimi.mm"
include "com12.mm"
include "a1d.mm"
include "ralrimivv.mm"
include "adantl.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "albidv.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem reuind
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  assume reuind.1: |- ( x = y -> ( ph <-> ps ) )
  assume reuind.2: |- ( x = y -> A = B )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph y
  disjoint ph z
  disjoint ps x
  disjoint ps z
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint w x
  disjoint C w
  disjoint ph w
  assert |- ( ( A. x A. y ( ( ( A e. C /\ ph ) /\ ( B e. C /\ ps ) ) -> A = B ) /\ E. x ( A e. C /\ ph ) ) -> E! z e. C A. x ( ( A e. C /\ ph ) -> z = A ) )

  proof
    cA
    cC
    wcel
    #
    wph
    wa
    #
    cB
    cC
    wcel
    #
    wps
    wa
    #
    wa
    #
    cA
    cB
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @1
    vx
    wex
    #
    wa
    @1
    vz
    cv
    #
    cA
    wceq
    #
    wi
    #
    vx
    wal
    #
    vz
    cC
    wrex
    #
    @12
    @1
    vw
    cv
    #
    cA
    wceq
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    @9
    @14
    wceq
    #
    wi
    #
    vw
    cC
    wral
    vz
    cC
    wral
    #
    @12
    vz
    cC
    wreu
    @7
    @8
    @13
    @8
    @9
    cB
    wceq
    #
    wps
    wa
    #
    vy
    wex
    #
    vz
    cC
    wrex
    #
    @7
    @13
    @8
    @3
    vy
    wex
    #
    @25
    @1
    @3
    vx
    vy
    vx
    cv
    vy
    cv
    wceq
    #
    @0
    @2
    wph
    wps
    @27
    cA
    cB
    cC
    reuind.2
    eleq1d
    reuind.1
    anbi12d
    cbvexv
    @23
    vz
    cC
    wrex
    #
    vy
    wex
    @22
    vz
    cC
    wrex
    #
    wps
    wa
    #
    vy
    wex
    @25
    @26
    @28
    @30
    vy
    @22
    wps
    vz
    cC
    r19.41v
    exbii
    @23
    vz
    vy
    cC
    rexcom4
    @3
    @30
    vy
    @2
    @29
    wps
    vz
    cB
    cC
    risset
    anbi1i
    exbii
    3bitr4ri
    bitri
    @7
    @24
    @12
    vz
    cC
    @7
    @9
    cC
    wcel
    #
    @24
    @12
    @7
    @22
    @3
    wa
    #
    @11
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @31
    @24
    wa
    #
    @12
    wi
    #
    @6
    @33
    vx
    vy
    @6
    @4
    @10
    @22
    wb
    #
    wi
    #
    @33
    @5
    @38
    @4
    cA
    cB
    @9
    eqeq2
    imim2i
    @39
    @4
    @22
    @10
    wi
    #
    wi
    #
    @33
    @38
    @40
    @4
    @10
    @22
    biimpr
    imim2i
    @4
    @22
    wa
    #
    @10
    wi
    @32
    @1
    wa
    #
    @10
    wi
    @41
    @33
    @42
    @43
    @10
    @1
    @3
    @22
    an31
    imbi1i
    @4
    @22
    @10
    impexp
    @32
    @1
    @10
    impexp
    3bitr3i
    sylib
    syl
    2alimi
    @35
    @36
    @11
    wi
    #
    vx
    wal
    @37
    @34
    @44
    vx
    @34
    @32
    vy
    wex
    #
    @11
    wi
    @44
    @32
    @11
    vy
    19.23v
    @45
    @36
    @11
    @45
    @31
    @23
    wa
    #
    vy
    wex
    @36
    @32
    @46
    vy
    @32
    @2
    @23
    wa
    @46
    @22
    @2
    wps
    an12
    @23
    @31
    @2
    @22
    @31
    @2
    wb
    wps
    @9
    cB
    cC
    eleq1
    adantr
    pm5.32ri
    bitr4i
    exbii
    @31
    @23
    vy
    19.42v
    bitri
    imbi1i
    bitri
    albii
    @36
    @11
    vx
    19.21v
    bitri
    sylib
    expd
    reximdvai
    syl5bi
    imp
    @8
    @21
    @7
    @8
    @20
    vz
    vw
    cC
    cC
    @8
    @20
    @31
    @14
    cC
    wcel
    wa
    @18
    @8
    @19
    @18
    @1
    @19
    wi
    #
    vx
    wal
    @8
    @19
    wi
    @11
    @16
    @47
    vx
    @1
    @1
    @1
    wa
    #
    @11
    @16
    wa
    @10
    @15
    wa
    @19
    @1
    @48
    @1
    pm4.24
    biimpi
    @1
    @10
    @1
    @15
    prth
    @9
    @14
    cA
    eqtr3
    syl56
    alanimi
    @1
    @19
    vx
    19.23v
    sylib
    com12
    a1d
    ralrimivv
    adantl
    @12
    @17
    vz
    vw
    cC
    @19
    @11
    @16
    vx
    @19
    @10
    @15
    @1
    @9
    @14
    cA
    eqeq1
    imbi2d
    albidv
    reu4
    sylanbrc
end
