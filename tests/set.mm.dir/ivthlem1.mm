include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cicc.mm"
include "co.mm"
include "cfv.mm"
include "cxr.mm"
include "rexrd.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "cr.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "clt.mm"
include "simpld.mm"
include "breq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "wi.mm"
include "iccleub.mm"
include "3expia.mm"
include "syl2anc.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "jca.mm"

theorem ivthlem1
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cU: class U
  let cF: class F
  let vc: setvar c
  let vy: setvar y
  let cC: class C
  assume ivth.1: |- ( ph -> A e. RR )
  assume ivth.2: |- ( ph -> B e. RR )
  assume ivth.3: |- ( ph -> U e. RR )
  assume ivth.4: |- ( ph -> A < B )
  assume ivth.5: |- ( ph -> ( A [,] B ) C_ D )
  assume ivth.7: |- ( ph -> F e. ( D -cn-> CC ) )
  assume ivth.8: |- ( ( ph /\ x e. ( A [,] B ) ) -> ( F ` x ) e. RR )
  assume ivth.9: |- ( ph -> ( ( F ` A ) < U /\ U < ( F ` B ) ) )
  assume ivth.10: |- S = { x e. ( A [,] B ) | ( F ` x ) <_ U }

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint D x
  disjoint D z
  disjoint F x
  disjoint F z
  disjoint ph x
  disjoint ph z
  disjoint A x
  disjoint S x
  disjoint S z
  disjoint U x
  disjoint U z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint x y
  disjoint y z
  disjoint B y
  disjoint D c
  disjoint D y
  disjoint F c
  disjoint F y
  disjoint c ph
  disjoint ph y
  disjoint A c
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S y
  disjoint U c
  disjoint U y
  assert |- ( ph -> ( A e. S /\ A. z e. S z <_ B ) )

  proof
    wph
    cA
    cS
    wcel
    #
    vz
    cv
    #
    cB
    cle
    wbr
    #
    vz
    cS
    wral
    wph
    cA
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cU
    cle
    wbr
    #
    @0
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
    @4
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
    cA
    cB
    lbicc2
    syl3anc
    #
    wph
    @5
    cU
    wph
    @4
    vx
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    vx
    @3
    wral
    @5
    cr
    wcel
    #
    @11
    wph
    @14
    vx
    @3
    ivth.8
    ralrimiva
    @14
    @15
    vx
    cA
    @3
    @12
    cA
    wceq
    #
    @13
    @5
    cr
    @12
    cA
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    ivth.3
    wph
    @5
    cU
    clt
    wbr
    cU
    cB
    cF
    cfv
    clt
    wbr
    ivth.9
    simpld
    ltled
    @13
    cU
    cle
    wbr
    #
    @6
    vx
    cA
    @3
    cS
    @16
    @13
    @5
    cU
    cle
    @17
    breq1d
    ivth.10
    elrab2
    sylanbrc
    wph
    @2
    vz
    cS
    @1
    cS
    wcel
    @1
    @3
    wcel
    #
    wph
    @2
    cS
    @3
    @1
    cS
    @18
    vx
    @3
    crab
    @3
    ivth.10
    @18
    vx
    @3
    ssrab2
    eqsstri
    sseli
    wph
    @7
    @8
    @19
    @2
    wi
    @9
    @10
    @7
    @8
    @19
    @2
    cA
    cB
    @1
    iccleub
    3expia
    syl2anc
    syl5
    ralrimiv
    jca
end
