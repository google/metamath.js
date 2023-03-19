include "cs3.mm"
include "cv.mm"
include "ccgrg.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "chpg.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "trgcopy.mm"
include "wcel.mm"
include "cdif.mm"
include "copab.mm"
include "cstrkg.mm"
include "ad5antr.mm"
include "wo.mm"
include "wn.mm"
include "simpl.mm"
include "eleq1d.mm"
include "simpr.mm"
include "anbi12d.mm"
include "simpll.mm"
include "simplr.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "cbvrexdva.mm"
include "cbvopabv.mm"
include "simp-5r.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "simpld.mm"
include "simprd.mm"
include "trgcopyeulem.mm"
include "anasss.mm"
include "ex.mm"
include "ralrimivva.mm"
include "eqidd.mm"
include "id.mm"
include "s3eqd.mm"
include "breq2d.mm"
include "breq1.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem trgcopyeu
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vq: setvar q
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume trgcopy.p: |- P = ( Base ` G )
  assume trgcopy.m: |- .- = ( dist ` G )
  assume trgcopy.i: |- I = ( Itv ` G )
  assume trgcopy.l: |- L = ( LineG ` G )
  assume trgcopy.k: |- K = ( hlG ` G )
  assume trgcopy.g: |- ( ph -> G e. TarskiG )
  assume trgcopy.a: |- ( ph -> A e. P )
  assume trgcopy.b: |- ( ph -> B e. P )
  assume trgcopy.c: |- ( ph -> C e. P )
  assume trgcopy.d: |- ( ph -> D e. P )
  assume trgcopy.e: |- ( ph -> E e. P )
  assume trgcopy.f: |- ( ph -> F e. P )
  assume trgcopy.1: |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) )
  assume trgcopy.2: |- ( ph -> -. ( D e. ( E L F ) \/ E = F ) )
  assume trgcopy.3: |- ( ph -> ( A .- B ) = ( D .- E ) )

  disjoint .- f
  disjoint A f
  disjoint B f
  disjoint C f
  disjoint D f
  disjoint E f
  disjoint F f
  disjoint G f
  disjoint I f
  disjoint L f
  disjoint P f
  disjoint f ph
  disjoint K f
  disjoint .- a
  disjoint .- b
  disjoint .- j
  disjoint .- k
  disjoint .- l
  disjoint .- q
  disjoint .- t
  disjoint .- v
  disjoint .- w
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint a b
  disjoint a f
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a q
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b f
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b q
  disjoint b t
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f q
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint j k
  disjoint j l
  disjoint j q
  disjoint j t
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k l
  disjoint k q
  disjoint k t
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint l q
  disjoint l t
  disjoint l v
  disjoint l w
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint q t
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A b
  disjoint A j
  disjoint A k
  disjoint A l
  disjoint A q
  disjoint A t
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B b
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B q
  disjoint B t
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C a
  disjoint C b
  disjoint C j
  disjoint C k
  disjoint C l
  disjoint C q
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D a
  disjoint D b
  disjoint D j
  disjoint D k
  disjoint D l
  disjoint D q
  disjoint D t
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E a
  disjoint E b
  disjoint E j
  disjoint E k
  disjoint E l
  disjoint E q
  disjoint E t
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F a
  disjoint F b
  disjoint F j
  disjoint F k
  disjoint F l
  disjoint F q
  disjoint F t
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G a
  disjoint G b
  disjoint G j
  disjoint G k
  disjoint G l
  disjoint G q
  disjoint G t
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I a
  disjoint I b
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I q
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint L a
  disjoint L b
  disjoint L j
  disjoint L k
  disjoint L l
  disjoint L q
  disjoint L t
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint P a
  disjoint P b
  disjoint P j
  disjoint P k
  disjoint P l
  disjoint P q
  disjoint P t
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph q
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint K a
  disjoint K j
  disjoint K k
  disjoint K l
  assert |- ( ph -> E! f e. P ( <" A B C "> ( cgrG ` G ) <" D E f "> /\ f ( ( hpG ` G ) ` ( D L E ) ) F ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cD
    cE
    vf
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
    cF
    cD
    cE
    cL
    co
    #
    cG
    chpg
    cfv
    cfv
    #
    wbr
    #
    wa
    #
    vf
    cP
    wrex
    @8
    @0
    cD
    cE
    vk
    cv
    #
    cs3
    #
    @3
    wbr
    #
    @9
    cF
    @6
    wbr
    #
    wa
    #
    wa
    #
    @1
    @9
    wceq
    #
    wi
    #
    vk
    cP
    wral
    vf
    cP
    wral
    @8
    vf
    cP
    wreu
    wph
    cA
    cB
    cC
    cD
    cP
    vf
    cE
    cF
    cG
    cI
    cK
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    trgcopy.k
    trgcopy.g
    trgcopy.a
    trgcopy.b
    trgcopy.c
    trgcopy.d
    trgcopy.e
    trgcopy.f
    trgcopy.1
    trgcopy.2
    trgcopy.3
    trgcopy
    wph
    @16
    vf
    vk
    cP
    cP
    wph
    @1
    cP
    wcel
    #
    @9
    cP
    wcel
    #
    @16
    wph
    @17
    wa
    #
    @18
    wa
    #
    @14
    @15
    @20
    @8
    @13
    @15
    @20
    @8
    wa
    #
    @11
    @12
    @15
    @21
    @11
    wa
    #
    @12
    wa
    #
    vt
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
    cL
    c.mi
    vx
    cv
    #
    cP
    @5
    cdif
    #
    wcel
    #
    vy
    cv
    #
    @25
    wcel
    #
    wa
    #
    vz
    cv
    #
    @24
    @27
    cI
    co
    #
    wcel
    #
    vz
    @5
    wrex
    #
    wa
    #
    vx
    vy
    copab
    @1
    @9
    va
    vb
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    trgcopy.k
    wph
    cG
    cstrkg
    wcel
    @17
    @18
    @8
    @11
    @12
    trgcopy.g
    ad5antr
    wph
    cA
    cP
    wcel
    @17
    @18
    @8
    @11
    @12
    trgcopy.a
    ad5antr
    wph
    cB
    cP
    wcel
    @17
    @18
    @8
    @11
    @12
    trgcopy.b
    ad5antr
    wph
    cC
    cP
    wcel
    @17
    @18
    @8
    @11
    @12
    trgcopy.c
    ad5antr
    wph
    cD
    cP
    wcel
    @17
    @18
    @8
    @11
    @12
    trgcopy.d
    ad5antr
    wph
    cE
    cP
    wcel
    @17
    @18
    @8
    @11
    @12
    trgcopy.e
    ad5antr
    wph
    cF
    cP
    wcel
    @17
    @18
    @8
    @11
    @12
    trgcopy.f
    ad5antr
    wph
    cA
    cB
    cC
    cL
    co
    wcel
    cB
    cC
    wceq
    wo
    wn
    @17
    @18
    @8
    @11
    @12
    trgcopy.1
    ad5antr
    wph
    cD
    cE
    cF
    cL
    co
    wcel
    cE
    cF
    wceq
    wo
    wn
    @17
    @18
    @8
    @11
    @12
    trgcopy.2
    ad5antr
    wph
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
    wceq
    @17
    @18
    @8
    @11
    @12
    trgcopy.3
    ad5antr
    @34
    va
    cv
    #
    @25
    wcel
    #
    vb
    cv
    #
    @25
    wcel
    #
    wa
    #
    vt
    cv
    #
    @35
    @37
    cI
    co
    #
    wcel
    #
    vt
    @5
    wrex
    #
    wa
    vx
    vy
    va
    vb
    @24
    @35
    wceq
    #
    @27
    @37
    wceq
    #
    wa
    #
    @29
    @39
    @33
    @43
    @46
    @26
    @36
    @28
    @38
    @46
    @24
    @35
    @25
    @44
    @45
    simpl
    eleq1d
    @46
    @27
    @37
    @25
    @44
    @45
    simpr
    eleq1d
    anbi12d
    @46
    @32
    @42
    vz
    vt
    @5
    @46
    @30
    @40
    wceq
    #
    wa
    #
    @30
    @40
    @31
    @41
    @46
    @47
    simpr
    @48
    @24
    @35
    @27
    @37
    cI
    @44
    @45
    @47
    simpll
    @44
    @45
    @47
    simplr
    oveq12d
    eleq12d
    cbvrexdva
    anbi12d
    cbvopabv
    wph
    @17
    @18
    @8
    @11
    @12
    simp-5r
    @19
    @18
    @8
    @11
    @12
    simp-4r
    @23
    @4
    @7
    @20
    @8
    @11
    @12
    simpllr
    #
    simpld
    @21
    @11
    @12
    simplr
    @23
    @4
    @7
    @49
    simprd
    @22
    @12
    simpr
    trgcopyeulem
    anasss
    anasss
    ex
    anasss
    ralrimivva
    @8
    @13
    vf
    vk
    cP
    @15
    @4
    @11
    @7
    @12
    @15
    @2
    @10
    @0
    @3
    @15
    cD
    cE
    @1
    @9
    cD
    cE
    @15
    cD
    eqidd
    @15
    cE
    eqidd
    @15
    id
    s3eqd
    breq2d
    @1
    @9
    cF
    @6
    breq1
    anbi12d
    reu4
    sylanbrc
end
