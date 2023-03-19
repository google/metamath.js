include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "w3a.mm"
include "cgr.mm"
include "cghomOLD.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "rngogrpo.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "rngogrphom.mm"
include "3jca.mm"
include "ghomdiv.mm"
include "sylan.mm"

theorem rngohomsub
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  assume rnghomsub.1: |- G = ( 1st ` R )
  assume rnghomsub.2: |- X = ran G
  assume rnghomsub.3: |- H = ( /g ` G )
  assume rnghomsub.4: |- J = ( 1st ` S )
  assume rnghomsub.5: |- K = ( /g ` J )


  assert |- ( ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) /\ ( A e. X /\ B e. X ) ) -> ( F ` ( A H B ) ) = ( ( F ` A ) K ( F ` B ) ) )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cF
    cR
    cS
    crnghom
    co
    wcel
    #
    w3a
    #
    cG
    cgr
    wcel
    #
    cJ
    cgr
    wcel
    #
    cF
    cG
    cJ
    cghomOLD
    co
    wcel
    #
    w3a
    cA
    cX
    wcel
    cB
    cX
    wcel
    wa
    cA
    cB
    cH
    co
    cF
    cfv
    cA
    cF
    cfv
    cB
    cF
    cfv
    cK
    co
    wceq
    @3
    @4
    @5
    @6
    @0
    @1
    @4
    @2
    cR
    cG
    rnghomsub.1
    rngogrpo
    3ad2ant1
    @1
    @0
    @5
    @2
    cS
    cJ
    rnghomsub.4
    rngogrpo
    3ad2ant2
    cR
    cS
    cF
    cG
    cJ
    rnghomsub.1
    rnghomsub.4
    rngogrphom
    3jca
    cA
    cB
    cK
    cH
    cF
    cG
    cJ
    cX
    rnghomsub.2
    rnghomsub.3
    rnghomsub.5
    ghomdiv
    sylan
end
