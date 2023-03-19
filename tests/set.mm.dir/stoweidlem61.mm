include "cv.mm"
include "c4.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cle.mm"
include "wa.mm"
include "caddc.mm"
include "cr.mm"
include "wrex.mm"
include "wral.mm"
include "cabs.mm"
include "c2.mm"
include "cc0.mm"
include "cfz.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "stoweidlem60.mm"
include "wcel.mm"
include "nfv.mm"
include "nfan.mm"
include "crp.mm"
include "wi.mm"
include "ad2antrr.mm"
include "fcnre.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "sselda.mm"
include "w3a.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "simplr.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprrr.mm"
include "simprrl.mm"
include "stoweidlem13.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syl3anc.mm"
include "ralimdaa.mm"
include "reximdva.mm"
include "mpd.mm"

theorem stoweidlem61
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vq: setvar q
  let vj: setvar j
  let vn: setvar n
  let vk: setvar k
  assume stoweidlem61.1: |- F/_ t F
  assume stoweidlem61.2: |- F/ t ph
  assume stoweidlem61.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem61.4: |- ( ph -> J e. Comp )
  assume stoweidlem61.5: |- T = U. J
  assume stoweidlem61.6: |- ( ph -> T =/= (/) )
  assume stoweidlem61.7: |- C = ( J Cn K )
  assume stoweidlem61.8: |- ( ph -> A C_ C )
  assume stoweidlem61.9: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem61.10: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem61.11: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem61.12: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem61.13: |- ( ph -> F e. C )
  assume stoweidlem61.14: |- ( ph -> A. t e. T 0 <_ ( F ` t ) )
  assume stoweidlem61.15: |- ( ph -> E e. RR+ )
  assume stoweidlem61.16: |- ( ph -> E < ( 1 / 3 ) )

  disjoint f g
  disjoint f q
  disjoint f r
  disjoint f t
  disjoint f x
  disjoint A f
  disjoint g q
  disjoint g r
  disjoint g t
  disjoint g x
  disjoint A g
  disjoint q r
  disjoint q t
  disjoint q x
  disjoint A q
  disjoint r t
  disjoint r x
  disjoint A r
  disjoint t x
  disjoint A t
  disjoint A x
  disjoint E f
  disjoint E g
  disjoint E q
  disjoint E r
  disjoint E t
  disjoint E x
  disjoint F f
  disjoint F g
  disjoint F q
  disjoint F r
  disjoint F x
  disjoint J f
  disjoint J g
  disjoint J r
  disjoint J t
  disjoint T f
  disjoint T g
  disjoint T q
  disjoint T r
  disjoint T t
  disjoint T x
  disjoint f ph
  disjoint g ph
  disjoint ph q
  disjoint ph r
  disjoint ph x
  disjoint K t
  disjoint f j
  disjoint f n
  disjoint g j
  disjoint g n
  disjoint j n
  disjoint j q
  disjoint j r
  disjoint j t
  disjoint j x
  disjoint A j
  disjoint n q
  disjoint n r
  disjoint n t
  disjoint n x
  disjoint A n
  disjoint E j
  disjoint E n
  disjoint F j
  disjoint F n
  disjoint T j
  disjoint T n
  disjoint j ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> E. g e. A A. t e. T ( abs ` ( ( g ` t ) - ( F ` t ) ) ) < ( 2 x. E ) )

  proof
    wph
    vj
    cv
    #
    c4
    c3
    cdiv
    co
    cmin
    co
    cE
    cmul
    co
    #
    vt
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    @3
    @0
    c1
    c3
    cdiv
    co
    #
    cmin
    co
    cE
    cmul
    co
    cle
    wbr
    #
    wa
    #
    @2
    vg
    cv
    #
    cfv
    #
    @0
    @5
    caddc
    co
    cE
    cmul
    co
    #
    clt
    wbr
    #
    @1
    @9
    clt
    wbr
    #
    wa
    #
    wa
    #
    vj
    cr
    wrex
    #
    vt
    cT
    wral
    #
    vg
    cA
    wrex
    @9
    @3
    cmin
    co
    cabs
    cfv
    c2
    cE
    cmul
    co
    clt
    wbr
    #
    vt
    cT
    wral
    #
    vg
    cA
    wrex
    wph
    vx
    vt
    cA
    vj
    cc0
    vn
    cv
    cfz
    co
    #
    @10
    @3
    cle
    wbr
    vt
    cT
    crab
    cmpt
    #
    cC
    vj
    @19
    @6
    vt
    cT
    crab
    cmpt
    #
    cT
    vf
    vg
    vj
    vn
    cE
    cF
    cJ
    cK
    vr
    vq
    stoweidlem61.1
    stoweidlem61.2
    stoweidlem61.3
    stoweidlem61.5
    stoweidlem61.7
    @21
    eqid
    @20
    eqid
    stoweidlem61.4
    stoweidlem61.6
    stoweidlem61.8
    stoweidlem61.9
    stoweidlem61.10
    stoweidlem61.11
    stoweidlem61.12
    stoweidlem61.13
    stoweidlem61.14
    stoweidlem61.15
    stoweidlem61.16
    stoweidlem60
    wph
    @16
    @18
    vg
    cA
    wph
    @8
    cA
    wcel
    #
    wa
    #
    @15
    @17
    vt
    cT
    wph
    @22
    vt
    stoweidlem61.2
    @22
    vt
    nfv
    nfan
    @23
    @2
    cT
    wcel
    #
    wa
    cE
    crp
    wcel
    #
    @3
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @15
    @17
    wi
    wph
    @25
    @22
    @24
    stoweidlem61.15
    ad2antrr
    wph
    @24
    @26
    @22
    wph
    cT
    cr
    @2
    cF
    wph
    cC
    cT
    cF
    cJ
    cK
    stoweidlem61.3
    stoweidlem61.5
    stoweidlem61.7
    stoweidlem61.13
    fcnre
    ffvelrnda
    adantlr
    @23
    cT
    cr
    @2
    @8
    @23
    cC
    cT
    @8
    cJ
    cK
    stoweidlem61.3
    stoweidlem61.5
    stoweidlem61.7
    wph
    cA
    cC
    @8
    stoweidlem61.8
    sselda
    fcnre
    ffvelrnda
    @25
    @26
    @27
    w3a
    #
    @14
    @17
    vj
    cr
    @28
    @0
    cr
    wcel
    #
    wa
    #
    @14
    @17
    @30
    @14
    wa
    vj
    cE
    @3
    @9
    @25
    @26
    @27
    @29
    @14
    simpll1
    @25
    @26
    @27
    @29
    @14
    simpll2
    @25
    @26
    @27
    @29
    @14
    simpll3
    @28
    @29
    @14
    simplr
    @30
    @4
    @6
    @13
    simprll
    @30
    @4
    @6
    @13
    simprlr
    @30
    @7
    @11
    @12
    simprrr
    @30
    @7
    @11
    @12
    simprrl
    stoweidlem13
    ex
    rexlimdva
    syl3anc
    ralimdaa
    reximdva
    mpd
end
