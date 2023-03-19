include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cin.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cv.mm"
include "crab.mm"
include "inrab.mm"
include "ixxval.mm"
include "ineqan12d.mm"
include "wceq.mm"
include "wb.mm"
include "3expa.mm"
include "adantlr.mm"
include "3expb.mm"
include "ancoms.mm"
include "adantll.mm"
include "anbi12d.mm"
include "an4.mm"
include "syl6bbr.mm"
include "rabbidva.mm"
include "an4s.mm"
include "3eqtr4a.mm"
include "ifcl.mm"
include "syl2an.mm"
include "eqtr4d.mm"

theorem ixxin
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cO: class O
  let vw: setvar w
  let cQ: class Q
  let cP: class P
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )
  assume ixxin.2: |- ( ( A e. RR* /\ C e. RR* /\ z e. RR* ) -> ( if ( A <_ C , C , A ) R z <-> ( A R z /\ C R z ) ) )
  assume ixxin.3: |- ( ( z e. RR* /\ B e. RR* /\ D e. RR* ) -> ( z S if ( B <_ D , B , D ) <-> ( z S B /\ z S D ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint C w
  disjoint D w
  disjoint O w
  disjoint Q w
  disjoint B w
  disjoint P w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W w
  disjoint X w
  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( C e. RR* /\ D e. RR* ) ) -> ( ( A O B ) i^i ( C O D ) ) = ( if ( A <_ C , C , A ) O if ( B <_ D , B , D ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cO
    co
    #
    cC
    cD
    cO
    co
    #
    cin
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cA
    cif
    #
    vz
    cv
    #
    cR
    wbr
    #
    @12
    cB
    cD
    cle
    wbr
    #
    cB
    cD
    cif
    #
    cS
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    #
    @11
    @15
    cO
    co
    #
    @6
    cA
    @12
    cR
    wbr
    #
    @12
    cB
    cS
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    #
    cC
    @12
    cR
    wbr
    #
    @12
    cD
    cS
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    #
    cin
    @22
    @26
    wa
    #
    vz
    cxr
    crab
    #
    @9
    @18
    @22
    @26
    vz
    cxr
    inrab
    @2
    @5
    @7
    @23
    @8
    @27
    vx
    vy
    vz
    cA
    cB
    cR
    cS
    cO
    ixx.1
    ixxval
    vx
    vy
    vz
    cC
    cD
    cR
    cS
    cO
    ixx.1
    ixxval
    ineqan12d
    @0
    @3
    @1
    @4
    @18
    @29
    wceq
    @0
    @3
    wa
    #
    @1
    @4
    wa
    #
    wa
    #
    @17
    @28
    vz
    cxr
    @32
    @12
    cxr
    wcel
    #
    wa
    #
    @17
    @20
    @24
    wa
    #
    @21
    @25
    wa
    #
    wa
    @28
    @34
    @13
    @35
    @16
    @36
    @30
    @33
    @13
    @35
    wb
    #
    @31
    @0
    @3
    @33
    @37
    ixxin.2
    3expa
    adantlr
    @31
    @33
    @16
    @36
    wb
    #
    @30
    @33
    @31
    @38
    @33
    @1
    @4
    @38
    ixxin.3
    3expb
    ancoms
    adantll
    anbi12d
    @20
    @21
    @24
    @25
    an4
    syl6bbr
    rabbidva
    an4s
    3eqtr4a
    @0
    @3
    @1
    @4
    @19
    @18
    wceq
    #
    @30
    @11
    cxr
    wcel
    #
    @15
    cxr
    wcel
    @39
    @31
    @3
    @0
    @40
    @10
    cC
    cA
    cxr
    ifcl
    ancoms
    @14
    cB
    cD
    cxr
    ifcl
    vx
    vy
    vz
    @11
    @15
    cR
    cS
    cO
    ixx.1
    ixxval
    syl2an
    an4s
    eqtr4d
end
