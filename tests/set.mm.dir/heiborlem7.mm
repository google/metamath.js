include "cv.mm"
include "cfv.mm"
include "c2nd.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "c3.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "3re.mm"
include "3pos.mm"
include "elrpii.mm"
include "rpdivcl.mm"
include "mpan2.mm"
include "cr.mm"
include "2re.mm"
include "1lt2.mm"
include "expnlbnd.mm"
include "mp3an23.mm"
include "syl.mm"
include "wa.mm"
include "cmul.mm"
include "wceq.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "rpcn.mm"
include "rpne0.mm"
include "3cn.mm"
include "divrec.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "adantl.mm"
include "breq1d.mm"
include "wb.mm"
include "nnrecred.mm"
include "rpre.mm"
include "pm3.2i.mm"
include "ltmuldiv2.mm"
include "mp3an3.mm"
include "syl2anr.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "cop.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "fvex.mm"
include "ovex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "rexbiia.mm"
include "sylibr.mm"
include "rgen.mm"

theorem heiborlem7
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
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vt: setvar t
  let cA: class A
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
  disjoint k n
  disjoint k r
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n r
  disjoint n u
  disjoint F n
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint G k
  disjoint G x
  disjoint k ph
  disjoint ph r
  disjoint ph x
  disjoint k m
  disjoint k v
  disjoint k z
  disjoint D k
  disjoint m n
  disjoint m r
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n v
  disjoint n z
  disjoint D n
  disjoint r v
  disjoint r z
  disjoint D r
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
  disjoint M k
  disjoint M m
  disjoint M r
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
  disjoint J k
  disjoint J m
  disjoint J n
  disjoint J r
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
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X r
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
  disjoint k t
  disjoint r t
  disjoint t u
  disjoint F t
  disjoint g k
  disjoint g t
  disjoint g x
  disjoint G g
  disjoint G t
  disjoint g r
  disjoint g ph
  disjoint ph t
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint m t
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint M g
  disjoint M t
  disjoint B g
  disjoint B t
  disjoint J g
  disjoint J t
  disjoint U g
  disjoint U t
  disjoint g ps
  disjoint ps t
  disjoint ps y
  disjoint ps z
  disjoint S t
  disjoint X g
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
  assert |- A. r e. RR+ E. k e. NN ( 2nd ` ( M ` k ) ) < r

  proof
    vk
    cv
    #
    cM
    cfv
    #
    c2nd
    cfv
    #
    vr
    cv
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    vr
    crp
    @3
    crp
    wcel
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
    @3
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    @5
    @6
    @10
    c1
    @7
    cdiv
    co
    #
    @3
    c3
    cdiv
    co
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    @6
    @12
    crp
    wcel
    #
    @14
    @6
    c3
    crp
    wcel
    @15
    c3
    3re
    3pos
    elrpii
    @3
    c3
    rpdivcl
    mpan2
    @15
    c2
    cr
    wcel
    c1
    c2
    clt
    wbr
    @14
    2re
    1lt2
    @12
    c2
    vk
    expnlbnd
    mp3an23
    syl
    @6
    @9
    @13
    vk
    cn
    @6
    @0
    cn
    wcel
    #
    wa
    #
    @9
    c3
    @11
    cmul
    co
    #
    @3
    clt
    wbr
    #
    @13
    @17
    @8
    @18
    @3
    clt
    @16
    @8
    @18
    wceq
    #
    @6
    @16
    @7
    crp
    wcel
    #
    @20
    @16
    @7
    @16
    c2
    cn
    wcel
    @0
    cn0
    wcel
    @7
    cn
    wcel
    2nn
    @0
    nnnn0
    c2
    @0
    nnexpcl
    sylancr
    #
    nnrpd
    @21
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    @20
    @7
    rpcn
    @7
    rpne0
    c3
    cc
    wcel
    @23
    @24
    @20
    3cn
    c3
    @7
    divrec
    mp3an1
    syl2anc
    syl
    adantl
    breq1d
    @16
    @11
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @19
    @13
    wb
    #
    @6
    @16
    @7
    @22
    nnrecred
    @3
    rpre
    @25
    @26
    c3
    cr
    wcel
    #
    cc0
    c3
    clt
    wbr
    #
    wa
    @27
    @28
    @29
    3re
    3pos
    pm3.2i
    @11
    @3
    c3
    ltmuldiv2
    mp3an3
    syl2anr
    bitrd
    rexbidva
    mpbird
    @4
    @9
    vk
    cn
    @16
    @2
    @8
    @3
    clt
    @16
    @2
    @0
    cS
    cfv
    #
    @8
    cop
    #
    c2nd
    cfv
    @8
    @16
    @1
    @31
    c2nd
    vn
    @0
    vn
    cv
    #
    cS
    cfv
    #
    c3
    c2
    @32
    cexp
    co
    #
    cdiv
    co
    #
    cop
    @31
    cn
    cM
    @32
    @0
    wceq
    #
    @33
    @30
    @35
    @8
    @32
    @0
    cS
    fveq2
    @36
    @34
    @7
    c3
    cdiv
    @32
    @0
    c2
    cexp
    oveq2
    oveq2d
    opeq12d
    heibor.12
    @30
    @8
    opex
    fvmpt
    fveq2d
    @30
    @8
    @0
    cS
    fvex
    c3
    @7
    cdiv
    ovex
    op2nd
    syl6eq
    breq1d
    rexbiia
    sylibr
    rgen
end
