include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "elun.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "elixx1.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "simplrr.mm"
include "wi.mm"
include "adantr.mm"
include "simpl3.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "3jca.mm"
include "simplrl.mm"
include "jaodan.mm"
include "biimpar.mm"
include "syldan.mm"
include "wn.mm"
include "exmid.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "jca.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "3anan12.mm"
include "biantrud.mm"
include "3bitr2d.mm"
include "orbi12d.mm"
include "mpbiri.mm"
include "impbida.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem ixxun
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cO: class O
  let cW: class W
  let cX: class X
  let cD: class D
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )
  assume ixxun.2: |- P = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x T z /\ z U y ) } )
  assume ixxun.3: |- ( ( B e. RR* /\ w e. RR* ) -> ( B T w <-> -. w S B ) )
  assume ixxun.4: |- Q = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z U y ) } )
  assume ixxun.5: |- ( ( w e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( w S B /\ B X C ) -> w U C ) )
  assume ixxun.6: |- ( ( A e. RR* /\ B e. RR* /\ w e. RR* ) -> ( ( A W B /\ B T w ) -> A R w ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint O w
  disjoint Q w
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W w
  disjoint X w
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A W B /\ B X C ) ) -> ( ( A O B ) u. ( B P C ) ) = ( A Q C ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    cW
    wbr
    #
    cB
    cC
    cX
    wbr
    #
    wa
    #
    wa
    #
    vw
    cA
    cB
    cO
    co
    #
    cB
    cC
    cP
    co
    #
    cun
    #
    cA
    cC
    cQ
    co
    #
    vw
    cv
    #
    @10
    wcel
    @12
    @8
    wcel
    #
    @12
    @9
    wcel
    #
    wo
    #
    @7
    @12
    @11
    wcel
    #
    @12
    @8
    @9
    elun
    @7
    @15
    @16
    @7
    @15
    @12
    cxr
    wcel
    #
    cA
    @12
    cR
    wbr
    #
    @12
    cC
    cU
    wbr
    #
    w3a
    #
    @16
    @7
    @13
    @20
    @14
    @7
    @13
    wa
    #
    @17
    @18
    @19
    @21
    @17
    @18
    @12
    cB
    cS
    wbr
    #
    @7
    @13
    @17
    @18
    @22
    w3a
    #
    @7
    @0
    @1
    @13
    @23
    wb
    @0
    @1
    @2
    @6
    simpl1
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    vx
    vy
    vz
    cA
    cB
    @12
    cR
    cS
    cO
    ixx.1
    elixx1
    syl2anc
    #
    biimpa
    #
    simp1d
    #
    @21
    @17
    @18
    @22
    @27
    simp2d
    @21
    @22
    @5
    @19
    @21
    @17
    @18
    @22
    @27
    simp3d
    @3
    @4
    @5
    @13
    simplrr
    @21
    @17
    @1
    @2
    @22
    @5
    wa
    @19
    wi
    @28
    @7
    @1
    @13
    @25
    adantr
    @7
    @2
    @13
    @0
    @1
    @2
    @6
    simpl3
    #
    adantr
    ixxun.5
    syl3anc
    mp2and
    3jca
    @7
    @14
    wa
    #
    @17
    @18
    @19
    @30
    @17
    cB
    @12
    cT
    wbr
    #
    @19
    @7
    @14
    @17
    @31
    @19
    w3a
    #
    @7
    @1
    @2
    @14
    @32
    wb
    @25
    @29
    vx
    vy
    vz
    cB
    cC
    @12
    cT
    cU
    cP
    ixxun.2
    elixx1
    syl2anc
    #
    biimpa
    #
    simp1d
    #
    @30
    @4
    @31
    @18
    @3
    @4
    @5
    @14
    simplrl
    @30
    @17
    @31
    @19
    @34
    simp2d
    @30
    @0
    @1
    @17
    @4
    @31
    wa
    @18
    wi
    @7
    @0
    @14
    @24
    adantr
    @7
    @1
    @14
    @25
    adantr
    @35
    ixxun.6
    syl3anc
    mp2and
    @30
    @17
    @31
    @19
    @34
    simp3d
    3jca
    jaodan
    @7
    @16
    @20
    @7
    @0
    @2
    @16
    @20
    wb
    @24
    @29
    vx
    vy
    vz
    cA
    cC
    @12
    cR
    cU
    cQ
    ixxun.4
    elixx1
    syl2anc
    #
    biimpar
    syldan
    @7
    @16
    wa
    #
    @15
    @22
    @22
    wn
    #
    wo
    @22
    exmid
    @37
    @13
    @22
    @14
    @38
    @37
    @13
    @17
    @18
    wa
    #
    @22
    wa
    #
    @22
    @7
    @13
    @40
    wb
    @16
    @7
    @13
    @23
    @40
    @26
    @17
    @18
    @22
    df-3an
    syl6bb
    adantr
    @37
    @39
    @22
    @37
    @17
    @18
    @37
    @17
    @18
    @19
    @7
    @16
    @20
    @36
    biimpa
    #
    simp1d
    #
    @37
    @17
    @18
    @19
    @41
    simp2d
    jca
    biantrurd
    bitr4d
    @37
    @14
    @31
    @17
    @19
    wa
    #
    wa
    #
    @31
    @38
    @7
    @14
    @44
    wb
    @16
    @7
    @14
    @32
    @44
    @33
    @17
    @31
    @19
    3anan12
    syl6bb
    adantr
    @37
    @43
    @31
    @37
    @17
    @19
    @42
    @37
    @17
    @18
    @19
    @41
    simp3d
    jca
    biantrud
    @37
    @1
    @17
    @31
    @38
    wb
    @7
    @1
    @16
    @25
    adantr
    @42
    ixxun.3
    syl2anc
    3bitr2d
    orbi12d
    mpbiri
    impbida
    syl5bb
    eqrdv
end
