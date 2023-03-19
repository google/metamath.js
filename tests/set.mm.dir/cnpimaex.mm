include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cuni.mm"
include "wf.mm"
include "ctop.mm"
include "w3a.mm"
include "eqid.mm"
include "iscnp2.mm"
include "simprbi.mm"
include "simprd.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl.mm"
include "3imp.mm"

theorem cnpimaex
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let vy: setvar y
  let cX: class X

  disjoint A x
  disjoint F x
  disjoint J x
  disjoint K x
  disjoint P x
  disjoint x y
  disjoint A y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint P y
  disjoint X x
  assert |- ( ( F e. ( ( J CnP K ) ` P ) /\ A e. K /\ ( F ` P ) e. A ) -> E. x e. J ( P e. x /\ ( F " x ) C_ A ) )

  proof
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cA
    cK
    wcel
    #
    cP
    cF
    cfv
    #
    cA
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    cF
    @4
    cima
    #
    cA
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @0
    @2
    vy
    cv
    #
    wcel
    #
    @5
    @6
    @10
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    @1
    @3
    @9
    wi
    #
    wi
    @0
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf
    #
    @16
    @0
    cJ
    ctop
    wcel
    cK
    ctop
    wcel
    cP
    @18
    wcel
    w3a
    @20
    @16
    wa
    vx
    vy
    cP
    cF
    cJ
    cK
    @18
    @19
    @18
    eqid
    @19
    eqid
    iscnp2
    simprbi
    simprd
    @15
    @17
    vy
    cA
    cK
    @10
    cA
    wceq
    #
    @11
    @3
    @14
    @9
    @10
    cA
    @2
    eleq2
    @21
    @13
    @8
    vx
    cJ
    @21
    @12
    @7
    @5
    @10
    cA
    @6
    sseq2
    anbi2d
    rexbidv
    imbi12d
    rspccv
    syl
    3imp
end
