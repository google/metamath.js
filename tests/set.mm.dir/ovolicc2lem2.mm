include "cn.mm"
include "wcel.mm"
include "wn.mm"
include "cfv.mm"
include "c2nd.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "cr.mm"
include "adantr.mm"
include "cxp.mm"
include "wf.mm"
include "cin.mm"
include "wss.mm"
include "inss2.mm"
include "fss.mm"
include "sylancl.mm"
include "cicc.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "algrf.mm"
include "ffvelrnda.mm"
include "cv.mm"
include "wceq.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "xp2nd.mm"
include "syl.mm"
include "ltnled.mm"
include "simprl.mm"
include "c1st.mm"
include "wex.mm"
include "adantrr.mm"
include "simprd.mm"
include "n0.mm"
include "xp1st.mm"
include "w3a.mm"
include "simpr.mm"
include "elin.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "simp1d.mm"
include "ovolicc2lem1.mm"
include "syldan.mm"
include "simp2d.mm"
include "simp3d.mm"
include "ltletrd.mm"
include "exlimddv.mm"
include "simprr.mm"
include "mpbir3and.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "sylanbrc.mm"
include "expr.mm"
include "sylbird.mm"
include "con1d.mm"
include "impr.mm"

theorem ovolicc2lem2
  let wph: wff ph
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cP: class P
  let cX: class X
  assume ovolicc.1: |- ( ph -> A e. RR )
  assume ovolicc.2: |- ( ph -> B e. RR )
  assume ovolicc.3: |- ( ph -> A <_ B )
  assume ovolicc2.4: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovolicc2.5: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ovolicc2.6: |- ( ph -> U e. ( ~P ran ( (,) o. F ) i^i Fin ) )
  assume ovolicc2.7: |- ( ph -> ( A [,] B ) C_ U. U )
  assume ovolicc2.8: |- ( ph -> G : U --> NN )
  assume ovolicc2.9: |- ( ( ph /\ t e. U ) -> ( ( (,) o. F ) ` ( G ` t ) ) = t )
  assume ovolicc2.10: |- T = { u e. U | ( u i^i ( A [,] B ) ) =/= (/) }
  assume ovolicc2.11: |- ( ph -> H : T --> T )
  assume ovolicc2.12: |- ( ( ph /\ t e. T ) -> if ( ( 2nd ` ( F ` ( G ` t ) ) ) <_ B , ( 2nd ` ( F ` ( G ` t ) ) ) , B ) e. ( H ` t ) )
  assume ovolicc2.13: |- ( ph -> A e. C )
  assume ovolicc2.14: |- ( ph -> C e. T )
  assume ovolicc2.15: |- K = seq 1 ( ( H o. 1st ) , ( NN X. { C } ) )
  assume ovolicc2.16: |- W = { n e. NN | B e. ( K ` n ) }

  disjoint n t
  disjoint n u
  disjoint A n
  disjoint t u
  disjoint A t
  disjoint A u
  disjoint B n
  disjoint B t
  disjoint B u
  disjoint H t
  disjoint C n
  disjoint C t
  disjoint F n
  disjoint F t
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint G n
  disjoint G t
  disjoint W n
  disjoint n ph
  disjoint ph t
  disjoint T n
  disjoint T t
  disjoint N n
  disjoint N t
  disjoint N u
  disjoint U n
  disjoint U t
  disjoint U u
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
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
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
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C m
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
  disjoint F x
  disjoint F y
  disjoint i u
  disjoint i z
  disjoint K i
  disjoint j u
  disjoint j z
  disjoint K j
  disjoint K k
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
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T f
  disjoint T h
  disjoint T k
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint S h
  disjoint S z
  disjoint U h
  disjoint U x
  disjoint U z
  disjoint X t
  assert |- ( ( ph /\ ( N e. NN /\ -. N e. W ) ) -> ( 2nd ` ( F ` ( G ` ( K ` N ) ) ) ) <_ B )

  proof
    wph
    cN
    cn
    wcel
    #
    cN
    cW
    wcel
    #
    wn
    cN
    cK
    cfv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    c2nd
    cfv
    #
    cB
    cle
    wbr
    #
    wph
    @0
    wa
    #
    @6
    @1
    @7
    @6
    wn
    cB
    @5
    clt
    wbr
    #
    @1
    @7
    cB
    @5
    wph
    cB
    cr
    wcel
    #
    @0
    ovolicc.2
    adantr
    @7
    @4
    cr
    cr
    cxp
    #
    wcel
    #
    @5
    cr
    wcel
    @7
    cn
    @10
    @3
    cF
    wph
    cn
    @10
    cF
    wf
    #
    @0
    wph
    cn
    cle
    @10
    cin
    #
    cF
    wf
    @13
    @10
    wss
    @12
    ovolicc2.5
    cle
    @10
    inss2
    cn
    @13
    @10
    cF
    fss
    sylancl
    adantr
    @7
    cU
    cn
    @2
    cG
    wph
    cU
    cn
    cG
    wf
    @0
    ovolicc2.8
    adantr
    @7
    @2
    cU
    wcel
    #
    @2
    cA
    cB
    cicc
    co
    #
    cin
    #
    c0
    wne
    #
    @7
    @2
    cT
    wcel
    @14
    @17
    wa
    #
    wph
    cn
    cT
    cN
    cK
    wph
    cC
    cK
    cT
    cH
    c1
    cn
    nnuz
    ovolicc2.15
    wph
    1zzd
    ovolicc2.14
    ovolicc2.11
    algrf
    ffvelrnda
    vu
    cv
    #
    @15
    cin
    #
    c0
    wne
    @17
    vu
    @2
    cU
    cT
    @19
    @2
    wceq
    @20
    @16
    c0
    @19
    @2
    @15
    ineq1
    neeq1d
    ovolicc2.10
    elrab2
    sylib
    #
    simpld
    ffvelrnd
    ffvelrnd
    #
    @4
    cr
    cr
    xp2nd
    syl
    ltnled
    wph
    @0
    @8
    @1
    wph
    @0
    @8
    wa
    #
    wa
    #
    @0
    cB
    @2
    wcel
    #
    @1
    wph
    @0
    @8
    simprl
    @24
    @25
    @9
    @4
    c1st
    cfv
    #
    cB
    clt
    wbr
    #
    @8
    wph
    @9
    @23
    ovolicc.2
    adantr
    @24
    vx
    cv
    #
    @16
    wcel
    #
    @27
    vx
    @24
    @17
    @29
    vx
    wex
    @24
    @14
    @17
    wph
    @0
    @18
    @8
    @21
    adantrr
    #
    simprd
    vx
    @16
    n0
    sylib
    @24
    @29
    wa
    #
    @26
    @28
    cB
    @24
    @26
    cr
    wcel
    #
    @29
    wph
    @0
    @32
    @8
    @7
    @11
    @32
    @22
    @4
    cr
    cr
    xp1st
    syl
    adantrr
    adantr
    @31
    @28
    cr
    wcel
    #
    cA
    @28
    cle
    wbr
    #
    @28
    cB
    cle
    wbr
    #
    @31
    @28
    @15
    wcel
    #
    @33
    @34
    @35
    w3a
    #
    @31
    @28
    @2
    wcel
    #
    @36
    @31
    @29
    @38
    @36
    wa
    @24
    @29
    simpr
    @28
    @2
    @15
    elin
    sylib
    #
    simprd
    wph
    @36
    @37
    wb
    #
    @23
    @29
    wph
    cA
    cr
    wcel
    @9
    @40
    ovolicc.1
    ovolicc.2
    cA
    cB
    @28
    elicc2
    syl2anc
    ad2antrr
    mpbid
    #
    simp1d
    wph
    @9
    @23
    @29
    ovolicc.2
    ad2antrr
    @31
    @33
    @26
    @28
    clt
    wbr
    #
    @28
    @5
    clt
    wbr
    #
    @31
    @38
    @33
    @42
    @43
    w3a
    #
    @31
    @38
    @36
    @39
    simpld
    @24
    @38
    @44
    wb
    #
    @29
    wph
    @23
    @14
    @45
    @24
    @14
    @17
    @30
    simpld
    #
    wph
    vt
    cA
    cB
    @28
    cS
    cU
    cF
    cG
    @2
    ovolicc.1
    ovolicc.2
    ovolicc.3
    ovolicc2.4
    ovolicc2.5
    ovolicc2.6
    ovolicc2.7
    ovolicc2.8
    ovolicc2.9
    ovolicc2lem1
    syldan
    adantr
    mpbid
    simp2d
    @31
    @33
    @34
    @35
    @41
    simp3d
    ltletrd
    exlimddv
    wph
    @0
    @8
    simprr
    wph
    @23
    @14
    @25
    @9
    @27
    @8
    w3a
    wb
    @46
    wph
    vt
    cA
    cB
    cB
    cS
    cU
    cF
    cG
    @2
    ovolicc.1
    ovolicc.2
    ovolicc.3
    ovolicc2.4
    ovolicc2.5
    ovolicc2.6
    ovolicc2.7
    ovolicc2.8
    ovolicc2.9
    ovolicc2lem1
    syldan
    mpbir3and
    cB
    vn
    cv
    #
    cK
    cfv
    #
    wcel
    @25
    vn
    cN
    cn
    cW
    @47
    cN
    wceq
    @48
    @2
    cB
    @47
    cN
    cK
    fveq2
    eleq2d
    ovolicc2.16
    elrab2
    sylanbrc
    expr
    sylbird
    con1d
    impr
end
