include "cv.mm"
include "cfv.mm"
include "c3.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cop.mm"
include "crp.mm"
include "cxp.mm"
include "wcel.mm"
include "cn.mm"
include "wral.mm"
include "wf.mm"
include "cn0.mm"
include "nnnn0.mm"
include "wa.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "inss1.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "elpwid.mm"
include "wbr.mm"
include "heiborlem4.mm"
include "fvex.mm"
include "vex.mm"
include "heiborlem2.mm"
include "simp2bi.mm"
include "syl.mm"
include "sseldd.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "wi.mm"
include "3re.mm"
include "3pos.mm"
include "elrpii.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "opelxpi.mm"
include "expcom.mm"
include "ralimia.mm"
include "fmpt.mm"

theorem heiborlem5
  let wph: wff ph
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
  let wps: wff ps
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
  disjoint ps y
  disjoint ps z
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
  assert |- ( ph -> M : NN --> ( X X. RR+ ) )

  proof
    wph
    vn
    cv
    #
    cS
    cfv
    #
    c3
    c2
    @0
    cexp
    co
    #
    cdiv
    co
    #
    cop
    #
    cX
    crp
    cxp
    #
    wcel
    #
    vn
    cn
    wral
    #
    cn
    @5
    cM
    wf
    wph
    @1
    cX
    wcel
    #
    vn
    cn
    wral
    #
    @7
    wph
    vk
    cv
    #
    cS
    cfv
    #
    cX
    wcel
    #
    vk
    cn
    wral
    @9
    wph
    @12
    vk
    cn
    @10
    cn
    wcel
    wph
    @10
    cn0
    wcel
    #
    @12
    @10
    nnnn0
    wph
    @13
    wa
    #
    @10
    cF
    cfv
    #
    cX
    @11
    @14
    @15
    cX
    @14
    cX
    cpw
    #
    cfn
    cin
    #
    @16
    @15
    @16
    cfn
    inss1
    wph
    cn0
    @17
    @10
    cF
    heibor.7
    ffvelrnda
    sseldi
    elpwid
    @14
    @11
    @10
    cG
    wbr
    #
    @11
    @15
    wcel
    #
    wph
    vx
    vy
    vz
    vv
    vu
    @10
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
    heiborlem4
    @18
    @13
    @19
    @11
    @10
    cB
    co
    cK
    wcel
    vy
    vv
    vu
    @11
    cB
    @10
    cD
    cU
    vn
    cF
    cG
    cJ
    cK
    heibor.1
    heibor.3
    heibor.4
    @10
    cS
    fvex
    vk
    vex
    heiborlem2
    simp2bi
    syl
    sseldd
    sylan2
    ralrimiva
    @12
    @8
    vk
    vn
    cn
    vk
    vn
    weq
    @11
    @1
    cX
    @10
    @0
    cS
    fveq2
    eleq1d
    cbvralv
    sylib
    @8
    @6
    vn
    cn
    @0
    cn
    wcel
    #
    @3
    crp
    wcel
    #
    @8
    @6
    wi
    @20
    c3
    crp
    wcel
    @2
    crp
    wcel
    @21
    c3
    3re
    3pos
    elrpii
    @20
    @2
    @20
    c2
    cn
    wcel
    @0
    cn0
    wcel
    @2
    cn
    wcel
    2nn
    @0
    nnnn0
    c2
    @0
    nnexpcl
    sylancr
    nnrpd
    c3
    @2
    rpdivcl
    sylancr
    @8
    @21
    @6
    @1
    @3
    cX
    crp
    opelxpi
    expcom
    syl
    ralimia
    syl
    vn
    cn
    @5
    @4
    cM
    heibor.12
    fmpt
    sylib
end
