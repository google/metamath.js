include "c1st.mm"
include "ccom.mm"
include "clm.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cuni.mm"
include "wrex.mm"
include "ctopon.mm"
include "wbr.mm"
include "cxmt.mm"
include "cms.mm"
include "cme.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "mopntopon.mm"
include "syl.mm"
include "cdm.mm"
include "cca.mm"
include "heiborlem5.mm"
include "heiborlem6.mm"
include "c2nd.mm"
include "clt.mm"
include "cn.mm"
include "crp.mm"
include "wral.mm"
include "heiborlem7.mm"
include "a1i.mm"
include "caubl.mm"
include "cmetcau.mm"
include "syl2anc.mm"
include "cha.mm"
include "wfun.mm"
include "wb.mm"
include "methaus.mm"
include "lmfun.mm"
include "funfvbrb.mm"
include "mpbid.mm"
include "lmcl.mm"
include "eleqtrrd.mm"
include "eluni2.mm"
include "sylib.mm"
include "wa.mm"
include "adantr.mm"
include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf.mm"
include "co.mm"
include "ciun.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wss.mm"
include "fvex.mm"
include "simprr.mm"
include "simprl.mm"
include "heiborlem8.mm"
include "rexlimddv.mm"

theorem heiborlem9
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vr: setvar r
  let vg: setvar g
  let cY: class Y
  let cZ: class Z
  assume heibor.1: |- J = ( MetOpen ` D )
  assume heibor.3: |- K = { u | -. E. v e. ( ~P U i^i Fin ) u C_ U. v }
  assume heibor.4: |- G = { <. y , n >. | ( n e. NN0 /\ y e. ( F ` n ) /\ ( y B n ) e. K ) }
  assume heibor.5: |- B = ( z e. X , m e. NN0 |-> ( z ( ball ` D ) ( 1 / ( 2 ^ m ) ) ) )
  assume heibor.6: |- ( ph -> D e. ( CMet ` X ) )
  assume heibor.7: |- ( ph -> F : NN0 --> ( ~P X i^i Fin ) )
  assume heibor.8: |- ( ph -> A. n e. NN0 X = U_ y e. ( F ` n ) ( y B n ) )
  assume heibor.9: |- ( ph -> A. x e. G ( ( T ` x ) G ( ( 2nd ` x ) + 1 ) /\ ( ( B ` x ) i^i ( ( T ` x ) B ( ( 2nd ` x ) + 1 ) ) ) e. K ) )
  assume heibor.10: |- ( ph -> C G 0 )
  assume heibor.11: |- S = seq 0 ( T , ( m e. NN0 |-> if ( m = 0 , C , ( m - 1 ) ) ) )
  assume heibor.12: |- M = ( n e. NN |-> <. ( S ` n ) , ( 3 / ( 2 ^ n ) ) >. )
  assume heibor.13: |- ( ph -> U C_ J )
  assume heiborlem9.14: |- ( ph -> U. U = X )

  disjoint B x
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint n u
  disjoint F n
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint ph x
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n v
  disjoint n z
  disjoint D n
  disjoint u v
  disjoint u z
  disjoint D u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint D v
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint M m
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B n
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint J m
  disjoint J n
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint U n
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint ps y
  disjoint ps z
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C m
  disjoint C n
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint n t
  disjoint A n
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n r
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint t u
  disjoint F t
  disjoint g k
  disjoint g t
  disjoint g x
  disjoint G g
  disjoint G k
  disjoint G t
  disjoint g r
  disjoint g ph
  disjoint k ph
  disjoint ph r
  disjoint ph t
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k v
  disjoint k z
  disjoint D k
  disjoint m r
  disjoint m t
  disjoint r v
  disjoint r z
  disjoint D r
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint M g
  disjoint M k
  disjoint M r
  disjoint M t
  disjoint B g
  disjoint B t
  disjoint J g
  disjoint J k
  disjoint J r
  disjoint J t
  disjoint U g
  disjoint U t
  disjoint g ps
  disjoint ps t
  disjoint S k
  disjoint S t
  disjoint X g
  disjoint X k
  disjoint X r
  disjoint X t
  disjoint C t
  disjoint K g
  disjoint K t
  disjoint Y k
  disjoint Y t
  disjoint Y x
  disjoint Z k
  disjoint Z v
  disjoint Z x
  assert |- ( ph -> ps )

  proof
    wph
    c1st
    cM
    ccom
    #
    cJ
    clm
    cfv
    #
    cfv
    #
    vt
    cv
    #
    wcel
    #
    wps
    vt
    cU
    wph
    @2
    cU
    cuni
    #
    wcel
    @4
    vt
    cU
    wrex
    wph
    @2
    cX
    @5
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @0
    @2
    @1
    wbr
    #
    @2
    cX
    wcel
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @6
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cX
    cme
    cfv
    wcel
    @8
    heibor.6
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    3syl
    #
    cD
    cJ
    cX
    heibor.1
    mopntopon
    syl
    wph
    @0
    @1
    cdm
    wcel
    #
    @7
    wph
    @9
    @0
    cD
    cca
    cfv
    wcel
    @11
    heibor.6
    wph
    cD
    vk
    cM
    cX
    vr
    @10
    wph
    vx
    vy
    vz
    vv
    vu
    cB
    cC
    cD
    cS
    cT
    cU
    vm
    vn
    cF
    cG
    cJ
    cK
    cM
    cX
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    heibor.6
    heibor.7
    heibor.8
    heibor.9
    heibor.10
    heibor.11
    heibor.12
    heiborlem5
    wph
    vx
    vy
    vz
    vv
    vu
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    vm
    vn
    cF
    cG
    cJ
    cK
    cM
    cX
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    heibor.6
    heibor.7
    heibor.8
    heibor.9
    heibor.10
    heibor.11
    heibor.12
    heiborlem6
    vk
    cv
    cM
    cfv
    c2nd
    cfv
    vr
    cv
    clt
    wbr
    vk
    cn
    wrex
    vr
    crp
    wral
    wph
    wph
    vx
    vy
    vz
    vv
    vu
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    vm
    vn
    cF
    cG
    cJ
    cK
    cM
    cX
    vr
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    heibor.6
    heibor.7
    heibor.8
    heibor.9
    heibor.10
    heibor.11
    heibor.12
    heiborlem7
    a1i
    caubl
    cD
    @0
    cJ
    cX
    heibor.1
    cmetcau
    syl2anc
    wph
    cJ
    cha
    wcel
    #
    @1
    wfun
    @11
    @7
    wb
    wph
    @8
    @12
    @10
    cD
    cJ
    cX
    heibor.1
    methaus
    syl
    cJ
    lmfun
    @0
    @1
    funfvbrb
    3syl
    mpbid
    #
    @2
    @0
    cJ
    cX
    lmcl
    syl2anc
    heiborlem9.14
    eleqtrrd
    vt
    @2
    cU
    eluni2
    sylib
    wph
    @3
    cU
    wcel
    #
    @4
    wa
    #
    wa
    wps
    vx
    vy
    vz
    vv
    vu
    cB
    cC
    cD
    cS
    cT
    cU
    vm
    vn
    cF
    cG
    cJ
    cK
    cM
    cX
    @2
    @3
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    wph
    @9
    @15
    heibor.6
    adantr
    wph
    cn0
    cX
    cpw
    cfn
    cin
    cF
    wf
    @15
    heibor.7
    adantr
    wph
    cX
    vy
    vn
    cv
    #
    cF
    cfv
    vy
    cv
    @16
    cB
    co
    ciun
    wceq
    vn
    cn0
    wral
    @15
    heibor.8
    adantr
    wph
    vx
    cv
    #
    cT
    cfv
    #
    @17
    c2nd
    cfv
    c1
    caddc
    co
    #
    cG
    wbr
    @17
    cB
    cfv
    @18
    @19
    cB
    co
    cin
    cK
    wcel
    wa
    vx
    cG
    wral
    @15
    heibor.9
    adantr
    wph
    cC
    cc0
    cG
    wbr
    @15
    heibor.10
    adantr
    heibor.11
    heibor.12
    wph
    cU
    cJ
    wss
    @15
    heibor.13
    adantr
    @0
    @1
    fvex
    wph
    @14
    @4
    simprr
    wph
    @14
    @4
    simprl
    wph
    @7
    @15
    @13
    adantr
    heiborlem8
    rexlimddv
end
