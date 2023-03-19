include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wmo.mm"
include "wi.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "mobidv.mm"
include "wal.mm"
include "oveq2.mm"
include "mo4.mm"
include "simpr.mm"
include "oveq2d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "vex.mm"
include "caovass.mm"
include "caov12.mm"
include "eqtri.mm"
include "elexi.mm"
include "caovcom.mm"
include "3eqtr3g.mm"
include "eqtr3d.mm"
include "syl6eqel.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "simprd.mm"
include "id.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "3eqtr3d.mm"
include "ax-gen.mm"
include "mpgbir.mm"
include "vtoclg.mm"
include "moanimv.mm"
include "mpbir.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "simpld.mm"
include "ancri.mm"
include "moimi.mm"
include "ax-mp.mm"

theorem caovmo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let cC: class C
  let cD: class D
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cT: class T
  assume caovmo.2: |- B e. S
  assume caovmo.dom: |- dom F = ( S X. S )
  assume caovmo.3: |- -. (/) e. S
  assume caovmo.com: |- ( x F y ) = ( y F x )
  assume caovmo.ass: |- ( ( x F y ) F z ) = ( x F ( y F z ) )
  assume caovmo.id: |- ( x e. S -> ( x F B ) = x )

  disjoint A w
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint S w
  disjoint S x
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint u w
  disjoint A u
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- E* w ( A F w ) = B

  proof
    cA
    cS
    wcel
    #
    cA
    vw
    cv
    #
    cF
    co
    #
    cB
    wceq
    #
    wa
    #
    vw
    wmo
    #
    @3
    vw
    wmo
    #
    @5
    @0
    @6
    wi
    vu
    cv
    #
    @1
    cF
    co
    #
    cB
    wceq
    #
    vw
    wmo
    #
    @6
    vu
    cA
    cS
    @7
    cA
    wceq
    #
    @9
    @3
    vw
    @11
    @8
    @2
    cB
    @7
    cA
    @1
    cF
    oveq1
    eqeq1d
    mobidv
    @10
    @9
    @7
    vv
    cv
    #
    cF
    co
    #
    cB
    wceq
    #
    wa
    #
    @1
    @12
    wceq
    #
    wi
    #
    vv
    wal
    vw
    @9
    @14
    vw
    vv
    @16
    @8
    @13
    cB
    @1
    @12
    @7
    cF
    oveq2
    eqeq1d
    mo4
    @17
    vv
    @15
    @1
    cB
    cF
    co
    #
    @12
    cB
    cF
    co
    #
    @1
    @12
    @15
    @1
    @13
    cF
    co
    #
    @18
    @19
    @15
    @13
    cB
    @1
    cF
    @9
    @14
    simpr
    #
    oveq2d
    @15
    @8
    @12
    cF
    co
    #
    cB
    @12
    cF
    co
    @20
    @19
    @15
    @8
    cB
    @12
    cF
    @9
    @14
    simpl
    #
    oveq1d
    @22
    @7
    @1
    @12
    cF
    co
    cF
    co
    @20
    vx
    vy
    vz
    @7
    @1
    @12
    cF
    vu
    vex
    #
    vw
    vex
    #
    vv
    vex
    #
    caovmo.ass
    caovass
    vx
    vy
    vz
    @7
    @1
    @12
    cF
    @24
    @25
    @26
    caovmo.com
    caovmo.ass
    caov12
    eqtri
    vx
    vy
    cB
    @12
    cF
    cB
    cS
    caovmo.2
    elexi
    @26
    caovmo.com
    caovcom
    3eqtr3g
    eqtr3d
    @15
    @1
    cS
    wcel
    #
    @18
    @1
    wceq
    #
    @15
    @7
    cS
    wcel
    #
    @27
    @15
    @8
    cS
    wcel
    @29
    @27
    wa
    @15
    @8
    cB
    cS
    @23
    caovmo.2
    syl6eqel
    @7
    @1
    cS
    cF
    caovmo.dom
    caovmo.3
    ndmovrcl
    syl
    simprd
    vx
    cv
    #
    cB
    cF
    co
    #
    @30
    wceq
    #
    @28
    vx
    @1
    cS
    @30
    @1
    wceq
    #
    @31
    @18
    @30
    @1
    @30
    @1
    cB
    cF
    oveq1
    @33
    id
    eqeq12d
    caovmo.id
    vtoclga
    syl
    @15
    @12
    cS
    wcel
    #
    @19
    @12
    wceq
    #
    @15
    @29
    @34
    @15
    @13
    cS
    wcel
    @29
    @34
    wa
    @15
    @13
    cB
    cS
    @21
    caovmo.2
    syl6eqel
    @7
    @12
    cS
    cF
    caovmo.dom
    caovmo.3
    ndmovrcl
    syl
    simprd
    @32
    @35
    vx
    @12
    cS
    @30
    @12
    wceq
    #
    @31
    @19
    @30
    @12
    @30
    @12
    cB
    cF
    oveq1
    @36
    id
    eqeq12d
    caovmo.id
    vtoclga
    syl
    3eqtr3d
    ax-gen
    mpgbir
    vtoclg
    @0
    @3
    vw
    moanimv
    mpbir
    @3
    @4
    vw
    @3
    @0
    @3
    @0
    @27
    @3
    @2
    cS
    wcel
    #
    @0
    @27
    wa
    @3
    @37
    cB
    cS
    wcel
    caovmo.2
    @2
    cB
    cS
    eleq1
    mpbiri
    cA
    @1
    cS
    cF
    caovmo.dom
    caovmo.3
    ndmovrcl
    syl
    simpld
    ancri
    moimi
    ax-mp
end
