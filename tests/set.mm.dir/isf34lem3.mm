include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "ccnv.mm"
include "compsscnv.mm"
include "imaeq1i.mm"
include "wf1.mm"
include "wceq.mm"
include "crpss.mm"
include "wiso.mm"
include "wf1o.mm"
include "compssiso.mm"
include "isof1o.mm"
include "f1of1.mm"
include "3syl.mm"
include "f1imacnv.mm"
include "sylan.mm"
include "syl5eqr.mm"

theorem isf34lem3
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cG: class G
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint A x
  disjoint V x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- ( ( A e. V /\ X C_ ~P A ) -> ( F " ( F " X ) ) = X )

  proof
    cA
    cV
    wcel
    #
    cX
    cA
    cpw
    #
    wss
    #
    wa
    cF
    cF
    cX
    cima
    #
    cima
    cF
    ccnv
    #
    @3
    cima
    #
    cX
    @4
    cF
    @3
    vx
    cA
    cF
    compss.a
    compsscnv
    imaeq1i
    @0
    @1
    @1
    cF
    wf1
    #
    @2
    @5
    cX
    wceq
    @0
    @1
    @1
    crpss
    crpss
    ccnv
    #
    cF
    wiso
    @1
    @1
    cF
    wf1o
    @6
    vx
    cA
    cF
    cV
    compss.a
    compssiso
    @1
    @1
    crpss
    @7
    cF
    isof1o
    @1
    @1
    cF
    f1of1
    3syl
    @1
    @1
    cX
    cF
    f1imacnv
    sylan
    syl5eqr
end
