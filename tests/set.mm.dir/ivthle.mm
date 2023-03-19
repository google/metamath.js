include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "cicc.mm"
include "co.mm"
include "wrex.mm"
include "wa.mm"
include "cioo.mm"
include "wss.mm"
include "ioossicc.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "cc.mm"
include "ccncf.mm"
include "adantlr.mm"
include "simpr.mm"
include "ivth.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "anassrs.mm"
include "cxr.mm"
include "cle.mm"
include "rexrd.mm"
include "ltled.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "sylan.mm"
include "wo.mm"
include "simprd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "leloed.mm"
include "mpbid.mm"
include "mpjaodan.mm"
include "lbicc2.mm"
include "eqeq1d.mm"
include "simpld.mm"

theorem ivthle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cF: class F
  let vc: setvar c
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  assume ivth.1: |- ( ph -> A e. RR )
  assume ivth.2: |- ( ph -> B e. RR )
  assume ivth.3: |- ( ph -> U e. RR )
  assume ivth.4: |- ( ph -> A < B )
  assume ivth.5: |- ( ph -> ( A [,] B ) C_ D )
  assume ivth.7: |- ( ph -> F e. ( D -cn-> CC ) )
  assume ivth.8: |- ( ( ph /\ x e. ( A [,] B ) ) -> ( F ` x ) e. RR )
  assume ivthle.9: |- ( ph -> ( ( F ` A ) <_ U /\ U <_ ( F ` B ) ) )

  disjoint c x
  disjoint B c
  disjoint B x
  disjoint D c
  disjoint D x
  disjoint F c
  disjoint F x
  disjoint c ph
  disjoint ph x
  disjoint A c
  disjoint A x
  disjoint U c
  disjoint U x
  disjoint c y
  disjoint c z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint F y
  disjoint F z
  disjoint ph y
  disjoint ph z
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U y
  disjoint U z
  assert |- ( ph -> E. c e. ( A [,] B ) ( F ` c ) = U )

  proof
    wph
    cA
    cF
    cfv
    #
    cU
    clt
    wbr
    #
    vc
    cv
    #
    cF
    cfv
    #
    cU
    wceq
    #
    vc
    cA
    cB
    cicc
    co
    #
    wrex
    #
    @0
    cU
    wceq
    #
    wph
    @1
    wa
    cU
    cB
    cF
    cfv
    #
    clt
    wbr
    #
    @6
    cU
    @8
    wceq
    #
    wph
    @1
    @9
    @6
    cA
    cB
    cioo
    co
    #
    @5
    wss
    wph
    @1
    @9
    wa
    #
    wa
    #
    @4
    vc
    @11
    wrex
    @6
    cA
    cB
    ioossicc
    @13
    vx
    cA
    cB
    cD
    cU
    cF
    vc
    wph
    cA
    cr
    wcel
    @12
    ivth.1
    adantr
    wph
    cB
    cr
    wcel
    @12
    ivth.2
    adantr
    wph
    cU
    cr
    wcel
    @12
    ivth.3
    adantr
    wph
    cA
    cB
    clt
    wbr
    @12
    ivth.4
    adantr
    wph
    @5
    cD
    wss
    @12
    ivth.5
    adantr
    wph
    cF
    cD
    cc
    ccncf
    co
    wcel
    @12
    ivth.7
    adantr
    wph
    vx
    cv
    #
    @5
    wcel
    @14
    cF
    cfv
    #
    cr
    wcel
    #
    @12
    ivth.8
    adantlr
    wph
    @12
    simpr
    ivth
    @4
    vc
    @11
    @5
    ssrexv
    mpsyl
    anassrs
    wph
    @10
    @6
    @1
    wph
    cB
    @5
    wcel
    #
    @10
    @6
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @17
    wph
    cA
    ivth.1
    rexrd
    #
    wph
    cB
    ivth.2
    rexrd
    #
    wph
    cA
    cB
    ivth.1
    ivth.2
    ivth.4
    ltled
    #
    cA
    cB
    ubicc2
    syl3anc
    #
    @4
    @10
    vc
    cB
    @5
    @4
    cU
    @3
    wceq
    @2
    cB
    wceq
    #
    @10
    @3
    cU
    eqcom
    @25
    @3
    @8
    cU
    @2
    cB
    cF
    fveq2
    eqeq2d
    syl5bb
    rspcev
    sylan
    adantlr
    wph
    @9
    @10
    wo
    #
    @1
    wph
    cU
    @8
    cle
    wbr
    #
    @26
    wph
    @0
    cU
    cle
    wbr
    #
    @27
    ivthle.9
    simprd
    wph
    cU
    @8
    ivth.3
    wph
    @17
    @16
    vx
    @5
    wral
    #
    @8
    cr
    wcel
    #
    @24
    wph
    @16
    vx
    @5
    ivth.8
    ralrimiva
    #
    @16
    @30
    vx
    cB
    @5
    @14
    cB
    wceq
    @15
    @8
    cr
    @14
    cB
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    leloed
    mpbid
    adantr
    mpjaodan
    wph
    cA
    @5
    wcel
    #
    @7
    @6
    wph
    @18
    @19
    @20
    @32
    @21
    @22
    @23
    cA
    cB
    lbicc2
    syl3anc
    #
    @4
    @7
    vc
    cA
    @5
    @2
    cA
    wceq
    @3
    @0
    cU
    @2
    cA
    cF
    fveq2
    eqeq1d
    rspcev
    sylan
    wph
    @28
    @1
    @7
    wo
    wph
    @28
    @27
    ivthle.9
    simpld
    wph
    @0
    cU
    wph
    @32
    @29
    @0
    cr
    wcel
    #
    @33
    @31
    @16
    @34
    vx
    cA
    @5
    @14
    cA
    wceq
    @15
    @0
    cr
    @14
    cA
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    ivth.3
    leloed
    mpbid
    mpjaodan
end
