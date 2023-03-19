include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cz.mm"
include "cin.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cdm.mm"
include "cr.mm"
include "cpr.mm"
include "cpm.mm"
include "cn0.mm"
include "wf.mm"
include "ad2antrr.mm"
include "cvv.mm"
include "wss.mm"
include "cnex.mm"
include "a1i.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "cle.mm"
include "wbr.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "cxr.mm"
include "w3a.mm"
include "inss1.mm"
include "wb.mm"
include "0xr.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "nn0re.mm"
include "rexrd.mm"
include "id.mm"
include "pnfxr.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "syl.mm"
include "elicc1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp2d.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "dvnf.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "ffvelrnd.mm"
include "cn.mm"
include "faccl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "simplr.mm"
include "dvnbss.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "recnprss.mm"
include "sstrd.mm"
include "sseldd.mm"
include "subcld.mm"
include "expcld.mm"
include "mulcld.mm"

theorem taylfvallem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cX: class X
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  let cY: class Y
  let cT: class T
  assume taylfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylfval.f: |- ( ph -> F : A --> CC )
  assume taylfval.a: |- ( ph -> A C_ S )
  assume taylfval.n: |- ( ph -> ( N e. NN0 \/ N = +oo ) )
  assume taylfval.b: |- ( ( ph /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> B e. dom ( ( S Dn F ) ` k ) )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint N k
  disjoint S k
  disjoint X k
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a f
  disjoint a s
  disjoint F a
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint k s
  disjoint n s
  disjoint F n
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint a ph
  disjoint f ph
  disjoint n ph
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint Y x
  disjoint N a
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint S a
  disjoint S f
  disjoint S n
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint X x
  assert |- ( ( ( ph /\ X e. CC ) /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> ( ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) x. ( ( X - B ) ^ k ) ) e. CC )

  proof
    wph
    cX
    cc
    wcel
    #
    wa
    #
    vk
    cv
    #
    cc0
    cN
    cicc
    co
    #
    cz
    cin
    #
    wcel
    #
    wa
    #
    cB
    @2
    cS
    cF
    cdvn
    co
    cfv
    #
    cfv
    #
    @2
    cfa
    cfv
    #
    cdiv
    co
    cX
    cB
    cmin
    co
    #
    @2
    cexp
    co
    @6
    @8
    @9
    @6
    @7
    cdm
    #
    cc
    cB
    @7
    @6
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    @2
    cn0
    wcel
    #
    @11
    cc
    @7
    wf
    wph
    @13
    @0
    @5
    taylfval.s
    ad2antrr
    #
    wph
    @14
    @0
    @5
    wph
    cc
    cvv
    wcel
    #
    @13
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    @14
    @17
    wph
    cnex
    a1i
    taylfval.s
    taylfval.f
    taylfval.a
    cc
    cS
    cA
    cF
    cvv
    @12
    elpm2r
    syl22anc
    ad2antrr
    #
    @6
    @2
    cz
    wcel
    cc0
    @2
    cle
    wbr
    #
    @15
    @6
    @4
    cz
    @2
    @3
    cz
    inss2
    @1
    @5
    simpr
    #
    sseldi
    @6
    @2
    cxr
    wcel
    #
    @20
    @2
    cN
    cle
    wbr
    #
    @6
    @2
    @3
    wcel
    #
    @22
    @20
    @23
    w3a
    #
    @6
    @4
    @3
    @2
    @3
    cz
    inss1
    @21
    sseldi
    @6
    cc0
    cxr
    wcel
    cN
    cxr
    wcel
    #
    @24
    @25
    wb
    0xr
    wph
    @26
    @0
    @5
    wph
    cN
    cn0
    wcel
    #
    cN
    cpnf
    wceq
    #
    wo
    @26
    taylfval.n
    @27
    @26
    @28
    @27
    cN
    cN
    nn0re
    rexrd
    @28
    cN
    cpnf
    cxr
    @28
    id
    pnfxr
    syl6eqel
    jaoi
    syl
    ad2antrr
    cc0
    cN
    @2
    elicc1
    sylancr
    mpbid
    simp2d
    @2
    elnn0z
    sylanbrc
    #
    cS
    cF
    @2
    dvnf
    syl3anc
    wph
    @5
    cB
    @11
    wcel
    @0
    taylfval.b
    adantlr
    #
    ffvelrnd
    @6
    @9
    @6
    @15
    @9
    cn
    wcel
    @29
    @2
    faccl
    syl
    #
    nncnd
    @6
    @9
    @31
    nnne0d
    divcld
    @6
    @10
    @2
    @6
    cX
    cB
    wph
    @0
    @5
    simplr
    @6
    @11
    cc
    cB
    @6
    @11
    cA
    cc
    @6
    @11
    cF
    cdm
    #
    cA
    @6
    @13
    @14
    @15
    @11
    @32
    wss
    @16
    @19
    @29
    cS
    cF
    @2
    dvnbss
    syl3anc
    @6
    @18
    @32
    cA
    wceq
    wph
    @18
    @0
    @5
    taylfval.f
    ad2antrr
    cA
    cc
    cF
    fdm
    syl
    sseqtrd
    wph
    cA
    cc
    wss
    @0
    @5
    wph
    cA
    cS
    cc
    taylfval.a
    wph
    @13
    cS
    cc
    wss
    taylfval.s
    cS
    recnprss
    syl
    sstrd
    ad2antrr
    sstrd
    @30
    sseldd
    subcld
    @29
    expcld
    mulcld
end
