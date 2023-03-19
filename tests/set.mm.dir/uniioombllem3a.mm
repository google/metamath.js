include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cioo.mm"
include "ciun.mm"
include "wceq.mm"
include "covol.mm"
include "cr.mm"
include "wcel.mm"
include "ccom.mm"
include "cima.mm"
include "cuni.mm"
include "cn.mm"
include "cpw.mm"
include "wf.mm"
include "wfun.mm"
include "cxr.mm"
include "cxp.mm"
include "ioof.mm"
include "cle.mm"
include "cin.mm"
include "wss.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "fco.mm"
include "sylancr.mm"
include "ffun.mm"
include "funiunfv.mm"
include "3syl.mm"
include "elfznn.mm"
include "fvco3.mm"
include "syl2an.mm"
include "iuneq2dv.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "csu.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "ioossre.mm"
include "syl6eqss.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "fzfid.mm"
include "cmin.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "ovolioo.mm"
include "eqtrd.mm"
include "simp2d.mm"
include "simp1d.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "fsumrecl.mm"
include "cfn.mm"
include "jca.mm"
include "ovolfiniun.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "ovollecl.mm"
include "syl3anc.mm"

theorem uniioombllem3a
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let vj: setvar j
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vw: setvar w
  let cH: class H
  let cJ: class J
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
  assume uniioombl.m: |- ( ph -> M e. NN )
  assume uniioombl.m2: |- ( ph -> ( abs ` ( ( T ` M ) - sup ( ran T , RR* , < ) ) ) < C )
  assume uniioombl.k: |- K = U. ( ( (,) o. G ) " ( 1 ... M ) )

  disjoint j x
  disjoint F j
  disjoint F x
  disjoint G j
  disjoint G x
  disjoint K j
  disjoint K x
  disjoint A j
  disjoint A x
  disjoint C j
  disjoint C x
  disjoint M j
  disjoint M x
  disjoint j ph
  disjoint ph x
  disjoint T j
  disjoint T x
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
  disjoint j y
  disjoint j z
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
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a m
  disjoint a w
  disjoint G a
  disjoint i m
  disjoint i w
  disjoint G i
  disjoint j m
  disjoint j w
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
  disjoint G z
  disjoint K n
  disjoint K y
  disjoint K z
  disjoint A a
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint A z
  disjoint C a
  disjoint C i
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C y
  disjoint C z
  disjoint M i
  disjoint M k
  disjoint M n
  disjoint M w
  disjoint M y
  disjoint M z
  disjoint E m
  disjoint E n
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint J z
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
  disjoint k ph
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint T a
  disjoint T i
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T y
  disjoint T z
  assert |- ( ph -> ( K = U_ j e. ( 1 ... M ) ( (,) ` ( G ` j ) ) /\ ( vol* ` K ) e. RR ) )

  proof
    wph
    cK
    vj
    c1
    cM
    cfz
    co
    #
    vj
    cv
    #
    cG
    cfv
    #
    cioo
    cfv
    #
    ciun
    #
    wceq
    cK
    covol
    cfv
    #
    cr
    wcel
    #
    wph
    cK
    cioo
    cG
    ccom
    #
    @0
    cima
    cuni
    #
    @4
    uniioombl.k
    wph
    vj
    @0
    @1
    @7
    cfv
    #
    ciun
    #
    @8
    @4
    wph
    cn
    cr
    cpw
    #
    @7
    wf
    #
    @7
    wfun
    @10
    @8
    wceq
    wph
    cxr
    cxr
    cxp
    #
    @11
    cioo
    wf
    cn
    @13
    cG
    wf
    #
    @12
    ioof
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cG
    wf
    #
    @16
    @13
    wss
    @14
    uniioombl.g
    @16
    @15
    @13
    cle
    @15
    inss2
    #
    rexpssxrxp
    sstri
    cn
    @16
    @13
    cG
    fss
    sylancl
    cn
    @13
    @11
    cioo
    cG
    fco
    sylancr
    cn
    @11
    @7
    ffun
    vj
    @0
    @7
    funiunfv
    3syl
    wph
    vj
    @0
    @9
    @3
    wph
    @17
    @1
    cn
    wcel
    #
    @9
    @3
    wceq
    @1
    @0
    wcel
    #
    uniioombl.g
    @1
    cM
    elfznn
    #
    cn
    @16
    @1
    cioo
    cG
    fvco3
    syl2an
    iuneq2dv
    eqtr3d
    syl5eq
    #
    wph
    cK
    cr
    wss
    @0
    @3
    covol
    cfv
    #
    vj
    csu
    #
    cr
    wcel
    @5
    @24
    cle
    wbr
    @6
    wph
    cK
    @4
    cr
    @22
    wph
    @3
    cr
    wss
    #
    vj
    @0
    wral
    @4
    cr
    wss
    wph
    @25
    vj
    @0
    wph
    @20
    wa
    #
    @3
    @2
    c1st
    cfv
    #
    @2
    c2nd
    cfv
    #
    cioo
    co
    #
    cr
    @26
    @3
    @27
    @28
    cop
    #
    cioo
    cfv
    @29
    @26
    @2
    @30
    cioo
    @26
    @2
    @15
    wcel
    @2
    @30
    wceq
    @26
    @16
    @15
    @2
    @18
    wph
    @17
    @19
    @2
    @16
    wcel
    @20
    uniioombl.g
    @21
    cn
    @16
    @1
    cG
    ffvelrn
    syl2an
    sseldi
    @2
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @27
    @28
    cioo
    df-ov
    syl6eqr
    #
    @27
    @28
    ioossre
    syl6eqss
    #
    ralrimiva
    vj
    @0
    @3
    cr
    iunss
    sylibr
    eqsstrd
    wph
    @0
    @23
    vj
    wph
    c1
    cM
    fzfid
    #
    @26
    @23
    @28
    @27
    cmin
    co
    #
    cr
    @26
    @23
    @29
    covol
    cfv
    #
    @34
    @26
    @3
    @29
    covol
    @31
    fveq2d
    @26
    @27
    cr
    wcel
    #
    @28
    cr
    wcel
    #
    @27
    @28
    cle
    wbr
    #
    w3a
    #
    @35
    @34
    wceq
    wph
    @17
    @19
    @39
    @20
    uniioombl.g
    @21
    cG
    @1
    ovolfcl
    syl2an
    #
    @27
    @28
    ovolioo
    syl
    eqtrd
    @26
    @28
    @27
    @26
    @36
    @37
    @38
    @40
    simp2d
    @26
    @36
    @37
    @38
    @40
    simp1d
    resubcld
    eqeltrd
    #
    fsumrecl
    wph
    @5
    @4
    covol
    cfv
    #
    @24
    cle
    wph
    cK
    @4
    covol
    @22
    fveq2d
    wph
    @0
    cfn
    wcel
    @25
    @23
    cr
    wcel
    #
    wa
    #
    vj
    @0
    wral
    @42
    @24
    cle
    wbr
    @33
    wph
    @44
    vj
    @0
    @26
    @25
    @43
    @32
    @41
    jca
    ralrimiva
    @0
    @3
    vj
    ovolfiniun
    syl2anc
    eqbrtrd
    cK
    @24
    ovollecl
    syl3anc
    jca
end
