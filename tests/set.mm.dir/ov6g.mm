include "wcel.mm"
include "cop.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "df-ov.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "eqid.mm"
include "biidd.mm"
include "copsex2g.mm"
include "mpbiri.mm"
include "3adant3.mm"
include "adantr.mm"
include "wi.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "wb.mm"
include "eqeq2d.mm"
include "eqcoms.mm"
include "pm5.32i.mm"
include "syl6bb.mm"
include "2exbidv.mm"
include "anbi2d.mm"
include "wmo.mm"
include "moeq.mm"
include "mosubop.mm"
include "a1i.mm"
include "coprab.mm"
include "copab.mm"
include "dfoprab2.mm"
include "eleq1.mm"
include "an12.mm"
include "bitr3i.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "bitri.mm"
include "opabbii.mm"
include "3eqtri.mm"
include "fvopab3ig.mm"
include "3ad2antl3.mm"
include "mpd.mm"
include "syl5eq.mm"

theorem ov6g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vw: setvar w
  assume ov6g.1: |- ( <. x , y >. = <. A , B >. -> R = S )
  assume ov6g.2: |- F = { <. <. x , y >. , z >. | ( <. x , y >. e. C /\ z = R ) }

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
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint R w
  disjoint S w
  assert |- ( ( ( A e. G /\ B e. H /\ <. A , B >. e. C ) /\ S e. J ) -> ( A F B ) = S )

  proof
    cA
    cG
    wcel
    #
    cB
    cH
    wcel
    #
    cA
    cB
    cop
    #
    cC
    wcel
    #
    w3a
    #
    cS
    cJ
    wcel
    #
    wa
    #
    cA
    cB
    cF
    co
    @2
    cF
    cfv
    #
    cS
    cA
    cB
    cF
    df-ov
    @6
    @2
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
    cS
    cS
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @7
    cS
    wceq
    #
    @4
    @14
    @5
    @0
    @1
    @14
    @3
    @0
    @1
    wa
    @14
    @12
    cS
    eqid
    @12
    @12
    vx
    vy
    cA
    cB
    cG
    cH
    @8
    cA
    wceq
    @9
    cB
    wceq
    wa
    @12
    biidd
    copsex2g
    mpbiri
    3adant3
    adantr
    @3
    @0
    @5
    @14
    @15
    wi
    @1
    vw
    cv
    #
    @10
    wceq
    #
    vz
    cv
    #
    cR
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @11
    @18
    cS
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    @14
    vw
    vz
    @2
    cS
    cC
    cJ
    cF
    @16
    @2
    wceq
    #
    @20
    @23
    vx
    vy
    @24
    @20
    @11
    @19
    wa
    @23
    @24
    @17
    @11
    @19
    @16
    @2
    @10
    eqeq1
    anbi1d
    @11
    @19
    @22
    @19
    @22
    wb
    @10
    @2
    @10
    @2
    wceq
    cR
    cS
    @18
    ov6g.1
    eqeq2d
    eqcoms
    pm5.32i
    syl6bb
    2exbidv
    @22
    @23
    @13
    vx
    vy
    @22
    @22
    @12
    @11
    @18
    cS
    cS
    eqeq1
    anbi2d
    2exbidv
    @21
    vz
    wmo
    @16
    cC
    wcel
    #
    @19
    vz
    vx
    vy
    @16
    vz
    cR
    moeq
    mosubop
    a1i
    cF
    @10
    cC
    wcel
    #
    @19
    wa
    #
    vx
    vy
    vz
    coprab
    @17
    @27
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    copab
    @25
    @21
    wa
    #
    vw
    vz
    copab
    ov6g.2
    @27
    vx
    vy
    vz
    vw
    dfoprab2
    @29
    @30
    vw
    vz
    @29
    @25
    @20
    wa
    #
    vy
    wex
    vx
    wex
    @30
    @28
    @31
    vx
    vy
    @28
    @17
    @25
    @19
    wa
    #
    wa
    @31
    @17
    @32
    @27
    @17
    @25
    @26
    @19
    @16
    @10
    cC
    eleq1
    anbi1d
    pm5.32i
    @17
    @25
    @19
    an12
    bitr3i
    2exbii
    @25
    @20
    vx
    vy
    19.42vv
    bitri
    opabbii
    3eqtri
    fvopab3ig
    3ad2antl3
    mpd
    syl5eq
end
