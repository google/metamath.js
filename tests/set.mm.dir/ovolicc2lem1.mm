include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cioo.mm"
include "co.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "ccom.mm"
include "cn.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "cxp.mm"
include "wf.mm"
include "cle.mm"
include "cin.mm"
include "wss.mm"
include "inss2.mm"
include "fss.mm"
include "sylancl.mm"
include "fvco3.mm"
include "sylan.mm"
include "syldan.mm"
include "cv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "cop.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "1st2nd2.mm"
include "syl.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "3eqtr3d.mm"
include "eleq2d.mm"
include "wb.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo2.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "bitrd.mm"

theorem ovolicc2lem1
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cW: class W
  let cT: class T
  let cN: class N
  assume ovolicc.1: |- ( ph -> A e. RR )
  assume ovolicc.2: |- ( ph -> B e. RR )
  assume ovolicc.3: |- ( ph -> A <_ B )
  assume ovolicc2.4: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovolicc2.5: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ovolicc2.6: |- ( ph -> U e. ( ~P ran ( (,) o. F ) i^i Fin ) )
  assume ovolicc2.7: |- ( ph -> ( A [,] B ) C_ U. U )
  assume ovolicc2.8: |- ( ph -> G : U --> NN )
  assume ovolicc2.9: |- ( ( ph /\ t e. U ) -> ( ( (,) o. F ) ` ( G ` t ) ) = t )

  disjoint A t
  disjoint B t
  disjoint F t
  disjoint G t
  disjoint ph t
  disjoint U t
  disjoint X t
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint H t
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C y
  disjoint C z
  disjoint h i
  disjoint h j
  disjoint F h
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint i u
  disjoint i z
  disjoint K i
  disjoint j u
  disjoint j z
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint f i
  disjoint f j
  disjoint G f
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint i m
  disjoint M i
  disjoint j m
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M t
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint W i
  disjoint W j
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint P k
  disjoint P y
  disjoint f ph
  disjoint g i
  disjoint g j
  disjoint g ph
  disjoint h ph
  disjoint i v
  disjoint i ph
  disjoint j v
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T f
  disjoint T h
  disjoint T k
  disjoint T n
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint N k
  disjoint N n
  disjoint N t
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint S h
  disjoint S z
  disjoint U h
  disjoint U n
  disjoint U u
  disjoint U x
  disjoint U z
  assert |- ( ( ph /\ X e. U ) -> ( P e. X <-> ( P e. RR /\ ( 1st ` ( F ` ( G ` X ) ) ) < P /\ P < ( 2nd ` ( F ` ( G ` X ) ) ) ) ) )

  proof
    wph
    cX
    cU
    wcel
    #
    wa
    #
    cP
    cX
    wcel
    cP
    cX
    cG
    cfv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cioo
    co
    #
    wcel
    #
    cP
    cr
    wcel
    @4
    cP
    clt
    wbr
    cP
    @5
    clt
    wbr
    w3a
    #
    @1
    cX
    @6
    cP
    @1
    @2
    cioo
    cF
    ccom
    #
    cfv
    #
    @3
    cioo
    cfv
    #
    cX
    @6
    wph
    @0
    @2
    cn
    wcel
    #
    @10
    @11
    wceq
    #
    wph
    cU
    cn
    cX
    cG
    ovolicc2.8
    ffvelrnda
    #
    wph
    cn
    cr
    cr
    cxp
    #
    cF
    wf
    #
    @12
    @13
    wph
    cn
    cle
    @15
    cin
    #
    cF
    wf
    @17
    @15
    wss
    @16
    ovolicc2.5
    cle
    @15
    inss2
    cn
    @17
    @15
    cF
    fss
    sylancl
    #
    cn
    @15
    @2
    cioo
    cF
    fvco3
    sylan
    syldan
    wph
    vt
    cv
    #
    cG
    cfv
    #
    @9
    cfv
    #
    @19
    wceq
    #
    vt
    cU
    wral
    @0
    @10
    cX
    wceq
    #
    wph
    @22
    vt
    cU
    ovolicc2.9
    ralrimiva
    @22
    @23
    vt
    cX
    cU
    @19
    cX
    wceq
    #
    @21
    @10
    @19
    cX
    @24
    @20
    @2
    @9
    @19
    cX
    cG
    fveq2
    fveq2d
    @24
    id
    eqeq12d
    rspccva
    sylan
    @1
    @11
    @4
    @5
    cop
    #
    cioo
    cfv
    @6
    @1
    @3
    @25
    cioo
    @1
    @3
    @15
    wcel
    #
    @3
    @25
    wceq
    @1
    cn
    @15
    @2
    cF
    wph
    @16
    @0
    @18
    adantr
    @14
    ffvelrnd
    #
    @3
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @4
    @5
    cioo
    df-ov
    syl6eqr
    3eqtr3d
    eleq2d
    @1
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @7
    @8
    wb
    #
    @1
    @26
    @28
    @27
    @3
    cr
    cr
    xp1st
    syl
    @1
    @26
    @29
    @27
    @3
    cr
    cr
    xp2nd
    syl
    @28
    @4
    cxr
    wcel
    @5
    cxr
    wcel
    @30
    @29
    @4
    rexr
    @5
    rexr
    @4
    @5
    cP
    elioo2
    syl2an
    syl2anc
    bitrd
end
