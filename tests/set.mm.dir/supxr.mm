include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "csup.mm"
include "wceq.mm"
include "simplr.mm"
include "simprl.mm"
include "xrub.mm"
include "biimpa.mm"
include "adantrl.mm"
include "w3a.mm"
include "wtru.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "eqsup.mm"
include "trud.mm"
include "syl3anc.mm"

theorem supxr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  assert |- ( ( ( A C_ RR* /\ B e. RR* ) /\ ( A. x e. A -. B < x /\ A. x e. RR ( x < B -> E. y e. A x < y ) ) ) -> sup ( A , RR* , < ) = B )

  proof
    cA
    cxr
    wss
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cB
    vx
    cv
    #
    clt
    wbr
    wn
    vx
    cA
    wral
    #
    @3
    cB
    clt
    wbr
    @3
    vy
    cv
    clt
    wbr
    vy
    cA
    wrex
    wi
    #
    vx
    cr
    wral
    #
    wa
    #
    wa
    @1
    @4
    @5
    vx
    cxr
    wral
    #
    cA
    cxr
    clt
    csup
    cB
    wceq
    #
    @0
    @1
    @7
    simplr
    @2
    @4
    @6
    simprl
    @2
    @6
    @8
    @4
    @2
    @6
    @8
    vx
    vy
    cA
    cB
    xrub
    biimpa
    adantrl
    @1
    @4
    @8
    w3a
    @9
    wi
    wtru
    vx
    vy
    cxr
    cA
    cB
    clt
    cxr
    clt
    wor
    wtru
    xrltso
    a1i
    eqsup
    trud
    syl3anc
end
