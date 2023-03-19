include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "fveq1i.mm"
include "cz.mm"
include "0z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "cvv.mm"
include "0nn0.mm"
include "w3a.mm"
include "relopabi.mm"
include "brrelexi.mm"
include "syl.mm"
include "iftrue.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "eqbrtrd.mm"
include "cin.mm"
include "wa.mm"
include "cop.mm"
include "df-br.mm"
include "c2nd.mm"
include "wral.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "fvex.mm"
include "vex.mm"
include "op2ndd.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ineq12d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspccv.mm"
include "syl5bi.mm"
include "cuz.mm"
include "seqp1.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "peano2nn0.mm"
include "cn.mm"
include "wn.mm"
include "nn0p1nn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalse.mm"
include "3syl.mm"
include "ovex.mm"
include "syl6eqel.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "ifbieq2d.mm"
include "syl2anc.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "biimprd.mm"
include "adantrd.mm"
include "syl9r.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem heiborlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
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
  let cX: class X
  let vt: setvar t
  let vk: setvar k
  let vr: setvar r
  let vg: setvar g
  let cM: class M
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

  disjoint B x
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
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
  disjoint t x
  disjoint t y
  disjoint A t
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
  disjoint M m
  disjoint M r
  disjoint M t
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
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
  assert |- ( ( ph /\ A e. NN0 ) -> ( S ` A ) G A )

  proof
    cA
    cn0
    wcel
    wph
    cA
    cS
    cfv
    #
    cA
    cG
    wbr
    #
    wph
    vx
    cv
    #
    cS
    cfv
    #
    @2
    cG
    wbr
    #
    wi
    wph
    cc0
    cS
    cfv
    #
    cc0
    cG
    wbr
    #
    wi
    wph
    vk
    cv
    #
    cS
    cfv
    #
    @7
    cG
    wbr
    #
    wi
    wph
    @7
    c1
    caddc
    co
    #
    cS
    cfv
    #
    @10
    cG
    wbr
    #
    wi
    wph
    @1
    wi
    vx
    vk
    cA
    @2
    cc0
    wceq
    #
    @4
    @6
    wph
    @13
    @3
    @5
    @2
    cc0
    cG
    @2
    cc0
    cS
    fveq2
    @13
    id
    breq12d
    imbi2d
    @2
    @7
    wceq
    #
    @4
    @9
    wph
    @14
    @3
    @8
    @2
    @7
    cG
    @2
    @7
    cS
    fveq2
    @14
    id
    breq12d
    imbi2d
    @2
    @10
    wceq
    #
    @4
    @12
    wph
    @15
    @3
    @11
    @2
    @10
    cG
    @2
    @10
    cS
    fveq2
    @15
    id
    breq12d
    imbi2d
    @2
    cA
    wceq
    #
    @4
    @1
    wph
    @16
    @3
    @0
    @2
    cA
    cG
    @2
    cA
    cS
    fveq2
    @16
    id
    breq12d
    imbi2d
    wph
    @5
    cC
    cc0
    cG
    wph
    @5
    cc0
    vm
    cn0
    vm
    cv
    #
    cc0
    wceq
    #
    cC
    @17
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cfv
    #
    cC
    @5
    cc0
    cT
    @21
    cc0
    cseq
    #
    cfv
    #
    @22
    cc0
    cS
    @23
    heibor.11
    fveq1i
    cc0
    cz
    wcel
    @24
    @22
    wceq
    0z
    cT
    @21
    cc0
    seq1
    ax-mp
    eqtri
    wph
    cc0
    cn0
    wcel
    cC
    cvv
    wcel
    #
    @22
    cC
    wceq
    0nn0
    wph
    cC
    cc0
    cG
    wbr
    @25
    heibor.10
    cC
    cc0
    cG
    vn
    cv
    #
    cn0
    wcel
    vy
    cv
    #
    @26
    cF
    cfv
    wcel
    @27
    @26
    cB
    co
    cK
    wcel
    w3a
    vy
    vn
    cG
    heibor.4
    relopabi
    brrelexi
    syl
    vm
    cc0
    @20
    cC
    cn0
    cvv
    @21
    @18
    cC
    @19
    iftrue
    @21
    eqid
    #
    fvmptg
    sylancr
    syl5eq
    heibor.10
    eqbrtrd
    @7
    cn0
    wcel
    #
    wph
    @9
    @12
    wph
    @9
    @8
    @7
    cT
    co
    #
    @10
    cG
    wbr
    #
    @8
    @7
    cB
    co
    #
    @30
    @10
    cB
    co
    #
    cin
    #
    cK
    wcel
    #
    wa
    #
    @29
    @12
    @9
    @8
    @7
    cop
    #
    cG
    wcel
    #
    wph
    @36
    @8
    @7
    cG
    df-br
    wph
    @2
    cT
    cfv
    #
    @2
    c2nd
    cfv
    #
    c1
    caddc
    co
    #
    cG
    wbr
    #
    @2
    cB
    cfv
    #
    @39
    @41
    cB
    co
    #
    cin
    #
    cK
    wcel
    #
    wa
    #
    vx
    cG
    wral
    @38
    @36
    wi
    heibor.9
    @47
    @36
    vx
    @37
    cG
    @2
    @37
    wceq
    #
    @42
    @31
    @46
    @35
    @48
    @39
    @30
    @41
    @10
    cG
    @48
    @39
    @37
    cT
    cfv
    @30
    @2
    @37
    cT
    fveq2
    @8
    @7
    cT
    df-ov
    syl6eqr
    #
    @48
    @40
    @7
    c1
    caddc
    @8
    @7
    @2
    @7
    cS
    fvex
    vk
    vex
    op2ndd
    oveq1d
    #
    breq12d
    @48
    @45
    @34
    cK
    @48
    @43
    @32
    @44
    @33
    @48
    @43
    @37
    cB
    cfv
    @32
    @2
    @37
    cB
    fveq2
    @8
    @7
    cB
    df-ov
    syl6eqr
    @48
    @39
    @30
    @41
    @10
    cB
    @49
    @50
    oveq12d
    ineq12d
    eleq1d
    anbi12d
    rspccv
    syl
    syl5bi
    @29
    @31
    @12
    @35
    @29
    @12
    @31
    @29
    @11
    @30
    @10
    cG
    @29
    @11
    @8
    @10
    @21
    cfv
    #
    cT
    co
    #
    @30
    @29
    @10
    @23
    cfv
    #
    @7
    @23
    cfv
    #
    @51
    cT
    co
    #
    @11
    @52
    @53
    @55
    wceq
    @7
    cc0
    cuz
    cfv
    cn0
    cT
    @21
    cc0
    @7
    seqp1
    nn0uz
    eleq2s
    @10
    cS
    @23
    heibor.11
    fveq1i
    @8
    @54
    @51
    cT
    @7
    cS
    @23
    heibor.11
    fveq1i
    oveq1i
    3eqtr4g
    @29
    @51
    @7
    @8
    cT
    @29
    @51
    @10
    cc0
    wceq
    #
    cC
    @10
    c1
    cmin
    co
    #
    cif
    #
    @57
    @7
    @29
    @10
    cn0
    wcel
    @58
    cvv
    wcel
    @51
    @58
    wceq
    @7
    peano2nn0
    @29
    @58
    @57
    cvv
    @29
    @10
    cn
    wcel
    #
    @56
    wn
    @58
    @57
    wceq
    @7
    nn0p1nn
    @59
    @10
    cc0
    @10
    nnne0
    neneqd
    @56
    cC
    @57
    iffalse
    3syl
    #
    @10
    c1
    cmin
    ovex
    syl6eqel
    vm
    @10
    @20
    @58
    cn0
    cvv
    @21
    @17
    @10
    wceq
    @18
    @56
    @19
    @57
    cC
    @17
    @10
    cc0
    eqeq1
    @17
    @10
    c1
    cmin
    oveq1
    ifbieq2d
    @28
    fvmptg
    syl2anc
    @60
    @29
    @7
    cc
    wcel
    c1
    cc
    wcel
    @57
    @7
    wceq
    @7
    nn0cn
    ax-1cn
    @7
    c1
    pncan
    sylancl
    3eqtrd
    oveq2d
    eqtrd
    breq1d
    biimprd
    adantrd
    syl9r
    a2d
    nn0ind
    impcom
end
