include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cioo.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "ivthlem3.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl.mm"

theorem ivth
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
  assume ivth.9: |- ( ph -> ( ( F ` A ) < U /\ U < ( F ` B ) ) )

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
  assert |- ( ph -> E. c e. ( A (,) B ) ( F ` c ) = U )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    #
    cU
    cle
    wbr
    #
    vy
    cA
    cB
    cicc
    co
    #
    crab
    #
    cr
    clt
    csup
    #
    cA
    cB
    cioo
    co
    #
    wcel
    @5
    cF
    cfv
    #
    cU
    wceq
    #
    wa
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
    @6
    wrex
    wph
    vx
    cA
    cB
    @5
    cD
    @4
    cU
    cF
    ivth.1
    ivth.2
    ivth.3
    ivth.4
    ivth.5
    ivth.7
    ivth.8
    ivth.9
    @2
    vx
    cv
    #
    cF
    cfv
    #
    cU
    cle
    wbr
    vy
    vx
    @3
    @0
    @12
    wceq
    @1
    @13
    cU
    cle
    @0
    @12
    cF
    fveq2
    breq1d
    cbvrabv
    @5
    eqid
    ivthlem3
    @11
    @8
    vc
    @5
    @6
    @9
    @5
    wceq
    @10
    @7
    cU
    @9
    @5
    cF
    fveq2
    eqeq1d
    rspcev
    syl
end
