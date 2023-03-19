include "cs3.mm"
include "ccgra.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "ccgrg.mm"
include "w3a.mm"
include "wrex.mm"
include "wceq.mm"
include "wa.mm"
include "iscgra.mm"
include "wcel.mm"
include "ad3antrrr.mm"
include "cstrkg.mm"
include "simpllr.mm"
include "simpr2.mm"
include "hlne2.mm"
include "co.mm"
include "eqcomd.mm"
include "tgcgrneq.mm"
include "necomd.mm"
include "hlid.mm"
include "eqid.mm"
include "simplr.mm"
include "simpr1.mm"
include "cgr3simp1.mm"
include "tgcgrcomlr.mm"
include "hlcgreulem.mm"
include "simpr3.mm"
include "jca32.mm"
include "simprrl.mm"
include "id.mm"
include "ad2antrl.mm"
include "wne.mm"
include "eqbrtrd.mm"
include "simprrr.mm"
include "3jca.mm"
include "impbida.mm"
include "rexbidva.mm"
include "r19.42v.mm"
include "syl6bb.mm"
include "wb.mm"
include "eqidd.mm"
include "s3eqd.mm"
include "breq2d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "ceqsrexv.mm"
include "syl.mm"
include "3bitrd.mm"

theorem iscgra1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let c.mi: class .-
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  assume iscgra.p: |- P = ( Base ` G )
  assume iscgra.i: |- I = ( Itv ` G )
  assume iscgra.k: |- K = ( hlG ` G )
  assume iscgra.g: |- ( ph -> G e. TarskiG )
  assume iscgra.a: |- ( ph -> A e. P )
  assume iscgra.b: |- ( ph -> B e. P )
  assume iscgra.c: |- ( ph -> C e. P )
  assume iscgra.d: |- ( ph -> D e. P )
  assume iscgra.e: |- ( ph -> E e. P )
  assume iscgra.f: |- ( ph -> F e. P )
  assume iscgra1.m: |- .- = ( dist ` G )
  assume iscgra1.1: |- ( ph -> A =/= B )
  assume iscgra1.2: |- ( ph -> ( A .- B ) = ( D .- E ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint E x
  disjoint F x
  disjoint K x
  disjoint ph x
  disjoint G x
  disjoint I x
  disjoint P x
  disjoint K y
  disjoint A a
  disjoint A b
  disjoint A y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B y
  disjoint C a
  disjoint C b
  disjoint C y
  disjoint D a
  disjoint D b
  disjoint D y
  disjoint E a
  disjoint E b
  disjoint E y
  disjoint F a
  disjoint F b
  disjoint F y
  disjoint K a
  disjoint K b
  disjoint K g
  disjoint K k
  disjoint K p
  disjoint K y
  disjoint a g
  disjoint a k
  disjoint a p
  disjoint b g
  disjoint b k
  disjoint b p
  disjoint g k
  disjoint g p
  disjoint g x
  disjoint g y
  disjoint k p
  disjoint k x
  disjoint k y
  disjoint p x
  disjoint p y
  disjoint ph y
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G k
  disjoint G p
  disjoint G y
  disjoint I a
  disjoint I b
  disjoint I g
  disjoint I k
  disjoint I p
  disjoint I y
  disjoint P a
  disjoint P b
  disjoint P g
  disjoint P k
  disjoint P p
  disjoint P y
  assert |- ( ph -> ( <" A B C "> ( cgrA ` G ) <" D E F "> <-> E. x e. P ( <" A B C "> ( cgrG ` G ) <" D E x "> /\ x ( K ` E ) F ) ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cD
    cE
    cF
    cs3
    cG
    ccgra
    cfv
    wbr
    @0
    vy
    cv
    #
    cE
    vx
    cv
    #
    cs3
    #
    cG
    ccgrg
    cfv
    #
    wbr
    #
    @1
    cD
    cE
    cK
    cfv
    #
    wbr
    #
    @2
    cF
    @6
    wbr
    #
    w3a
    #
    vx
    cP
    wrex
    #
    vy
    cP
    wrex
    @1
    cD
    wceq
    #
    @5
    @8
    wa
    #
    vx
    cP
    wrex
    #
    wa
    #
    vy
    cP
    wrex
    #
    @0
    cD
    cE
    @2
    cs3
    #
    @4
    wbr
    #
    @8
    wa
    #
    vx
    cP
    wrex
    #
    wph
    vy
    vx
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    cK
    iscgra.p
    iscgra.i
    iscgra.k
    iscgra.g
    iscgra.a
    iscgra.b
    iscgra.c
    iscgra.d
    iscgra.e
    iscgra.f
    iscgra
    wph
    @10
    @14
    vy
    cP
    wph
    @1
    cP
    wcel
    #
    wa
    #
    @10
    @11
    @12
    wa
    #
    vx
    cP
    wrex
    @14
    @21
    @9
    @22
    vx
    cP
    @21
    @2
    cP
    wcel
    #
    wa
    #
    @9
    @22
    @24
    @9
    wa
    #
    @11
    @5
    @8
    @25
    cE
    cB
    cA
    cD
    cP
    cG
    cI
    cK
    c.mi
    @1
    cD
    iscgra.p
    iscgra.i
    iscgra.k
    wph
    cE
    cP
    wcel
    #
    @20
    @23
    @9
    iscgra.e
    ad3antrrr
    #
    wph
    cB
    cP
    wcel
    @20
    @23
    @9
    iscgra.b
    ad3antrrr
    #
    wph
    cA
    cP
    wcel
    @20
    @23
    @9
    iscgra.a
    ad3antrrr
    #
    wph
    cG
    cstrkg
    wcel
    #
    @20
    @23
    @9
    iscgra.g
    ad3antrrr
    #
    wph
    cD
    cP
    wcel
    #
    @20
    @23
    @9
    iscgra.d
    ad3antrrr
    #
    iscgra1.m
    @25
    @1
    cD
    cE
    cP
    cG
    cI
    cK
    cstrkg
    iscgra.p
    iscgra.i
    iscgra.k
    wph
    @20
    @23
    @9
    simpllr
    #
    @33
    @27
    @31
    @24
    @5
    @7
    @8
    simpr2
    #
    hlne2
    #
    @25
    cA
    cB
    @25
    cD
    cE
    cA
    cB
    cP
    cG
    cI
    c.mi
    iscgra.p
    iscgra1.m
    iscgra.i
    @31
    @33
    @27
    @29
    @28
    @25
    cA
    cB
    c.mi
    co
    #
    cD
    cE
    c.mi
    co
    #
    wph
    @37
    @38
    wceq
    @20
    @23
    @9
    iscgra1.2
    ad3antrrr
    eqcomd
    #
    @36
    tgcgrneq
    necomd
    @34
    @33
    @35
    @25
    cD
    cE
    cE
    cP
    cG
    cI
    cK
    iscgra.p
    iscgra.i
    iscgra.k
    @33
    @27
    @27
    @31
    @36
    hlid
    @25
    @1
    cE
    cA
    cB
    cP
    cG
    cI
    c.mi
    iscgra.p
    iscgra1.m
    iscgra.i
    @31
    @34
    @27
    @29
    @28
    @25
    @37
    @1
    cE
    c.mi
    co
    @25
    cA
    cB
    cC
    @1
    cP
    @4
    cE
    @2
    cG
    cI
    c.mi
    iscgra.p
    iscgra1.m
    iscgra.i
    @4
    eqid
    @31
    @29
    @28
    wph
    cC
    cP
    wcel
    @20
    @23
    @9
    iscgra.c
    ad3antrrr
    @34
    @27
    @21
    @23
    @9
    simplr
    @24
    @5
    @7
    @8
    simpr1
    #
    cgr3simp1
    eqcomd
    tgcgrcomlr
    @25
    cD
    cE
    cA
    cB
    cP
    cG
    cI
    c.mi
    iscgra.p
    iscgra1.m
    iscgra.i
    @31
    @33
    @27
    @29
    @28
    @39
    tgcgrcomlr
    hlcgreulem
    @40
    @24
    @5
    @7
    @8
    simpr3
    jca32
    @24
    @22
    wa
    #
    @5
    @7
    @8
    @24
    @11
    @5
    @8
    simprrl
    @41
    @1
    cD
    cD
    @6
    @11
    @11
    @24
    @12
    @11
    id
    #
    ad2antrl
    @41
    cD
    cD
    cE
    cP
    cG
    cI
    cK
    iscgra.p
    iscgra.i
    iscgra.k
    wph
    @32
    @20
    @23
    @22
    iscgra.d
    ad3antrrr
    #
    @43
    wph
    @26
    @20
    @23
    @22
    iscgra.e
    ad3antrrr
    wph
    @30
    @20
    @23
    @22
    iscgra.g
    ad3antrrr
    wph
    cD
    cE
    wne
    @20
    @23
    @22
    wph
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    iscgra.p
    iscgra1.m
    iscgra.i
    iscgra.g
    iscgra.a
    iscgra.b
    iscgra.d
    iscgra.e
    iscgra1.2
    iscgra1.1
    tgcgrneq
    ad3antrrr
    hlid
    eqbrtrd
    @24
    @11
    @5
    @8
    simprrr
    3jca
    impbida
    rexbidva
    @11
    @12
    vx
    cP
    r19.42v
    syl6bb
    rexbidva
    wph
    @32
    @15
    @19
    wb
    iscgra.d
    @13
    @19
    vy
    cD
    cP
    @11
    @12
    @18
    vx
    cP
    @11
    @5
    @17
    @8
    @11
    @3
    @16
    @0
    @4
    @11
    @1
    cE
    @2
    @2
    cD
    cE
    @42
    @11
    cE
    eqidd
    @11
    @2
    eqidd
    s3eqd
    breq2d
    anbi1d
    rexbidv
    ceqsrexv
    syl
    3bitrd
end
