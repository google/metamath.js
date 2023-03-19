include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cioo.mm"
include "cin.mm"
include "c1st.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "c2nd.mm"
include "co.mm"
include "crn.mm"
include "cop.mm"
include "cr.mm"
include "cxp.mm"
include "wceq.mm"
include "inss2.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "ineq12d.mm"
include "cxr.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "simp1d.mm"
include "rexrd.mm"
include "simp2d.mm"
include "iooin.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "ioorebas.mm"
include "syl6eqel.mm"

theorem uniioombllem2a
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cJ: class J
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vm: setvar m
  let vw: setvar w
  let cK: class K
  let cM: class M
  let cH: class H
  let cN: class N
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.2: |- ( ph -> Disj_ x e. NN ( (,) ` ( F ` x ) ) )
  assume uniioombl.3: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume uniioombl.a: |- A = U. ran ( (,) o. F )
  assume uniioombl.e: |- ( ph -> ( vol* ` E ) e. RR )
  assume uniioombl.c: |- ( ph -> C e. RR+ )
  assume uniioombl.g: |- ( ph -> G : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.s: |- ( ph -> E C_ U. ran ( (,) o. G ) )
  assume uniioombl.t: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume uniioombl.v: |- ( ph -> sup ( ran T , RR* , < ) <_ ( ( vol* ` E ) + C ) )

  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G x
  disjoint G z
  disjoint A x
  disjoint A z
  disjoint C x
  disjoint C z
  disjoint J x
  disjoint J z
  disjoint ph x
  disjoint ph z
  disjoint T x
  disjoint T z
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint a m
  disjoint a w
  disjoint G a
  disjoint i m
  disjoint i w
  disjoint G i
  disjoint j m
  disjoint j w
  disjoint G j
  disjoint k m
  disjoint k w
  disjoint G k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n w
  disjoint G n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G y
  disjoint K j
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint A a
  disjoint A j
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint C a
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C y
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint E m
  disjoint E n
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint J n
  disjoint J y
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint N z
  disjoint S n
  disjoint S y
  disjoint a ph
  disjoint f m
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint T a
  disjoint T i
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T y
  assert |- ( ( ( ph /\ J e. NN ) /\ z e. NN ) -> ( ( (,) ` ( F ` z ) ) i^i ( (,) ` ( G ` J ) ) ) e. ran (,) )

  proof
    wph
    cJ
    cn
    wcel
    #
    wa
    #
    vz
    cv
    #
    cn
    wcel
    #
    wa
    #
    @2
    cF
    cfv
    #
    cioo
    cfv
    #
    cJ
    cG
    cfv
    #
    cioo
    cfv
    #
    cin
    #
    @5
    c1st
    cfv
    #
    @7
    c1st
    cfv
    #
    cle
    wbr
    @11
    @10
    cif
    #
    @5
    c2nd
    cfv
    #
    @7
    c2nd
    cfv
    #
    cle
    wbr
    @13
    @14
    cif
    #
    cioo
    co
    #
    cioo
    crn
    @4
    @9
    @10
    @13
    cioo
    co
    #
    @11
    @14
    cioo
    co
    #
    cin
    #
    @16
    @4
    @6
    @17
    @8
    @18
    @4
    @6
    @10
    @13
    cop
    #
    cioo
    cfv
    @17
    @4
    @5
    @20
    cioo
    @4
    @5
    cr
    cr
    cxp
    #
    wcel
    @5
    @20
    wceq
    @4
    cle
    @21
    cin
    #
    @21
    @5
    cle
    @21
    inss2
    #
    @1
    cn
    @22
    @2
    cF
    wph
    cn
    @22
    cF
    wf
    #
    @0
    uniioombl.1
    adantr
    #
    ffvelrnda
    sseldi
    @5
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @10
    @13
    cioo
    df-ov
    syl6eqr
    @1
    @8
    @18
    wceq
    @3
    @1
    @8
    @11
    @14
    cop
    #
    cioo
    cfv
    @18
    @1
    @7
    @26
    cioo
    @1
    @7
    @21
    wcel
    @7
    @26
    wceq
    @1
    @22
    @21
    @7
    @23
    wph
    cn
    @22
    cJ
    cG
    uniioombl.g
    ffvelrnda
    sseldi
    @7
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @11
    @14
    cioo
    df-ov
    syl6eqr
    adantr
    ineq12d
    @4
    @10
    cxr
    wcel
    @13
    cxr
    wcel
    @11
    cxr
    wcel
    #
    @14
    cxr
    wcel
    #
    @19
    @16
    wceq
    @4
    @10
    @4
    @10
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    @10
    @13
    cle
    wbr
    #
    @1
    @24
    @3
    @29
    @30
    @31
    w3a
    @25
    cF
    @2
    ovolfcl
    sylan
    #
    simp1d
    rexrd
    @4
    @13
    @4
    @29
    @30
    @31
    @32
    simp2d
    rexrd
    @1
    @27
    @3
    @1
    @11
    @1
    @11
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    @11
    @14
    cle
    wbr
    #
    wph
    cn
    @22
    cG
    wf
    @0
    @33
    @34
    @35
    w3a
    uniioombl.g
    cG
    cJ
    ovolfcl
    sylan
    #
    simp1d
    rexrd
    adantr
    @1
    @28
    @3
    @1
    @14
    @1
    @33
    @34
    @35
    @36
    simp2d
    rexrd
    adantr
    @10
    @13
    @11
    @14
    iooin
    syl22anc
    eqtrd
    @12
    @15
    ioorebas
    syl6eqel
end
