include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "cdif.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "difexg.mm"
include "adantr.mm"
include "cv.mm"
include "difeq2.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem isf34lem1
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
  assert |- ( ( A e. V /\ X C_ A ) -> ( F ` X ) = ( A \ X ) )

  proof
    cA
    cV
    wcel
    #
    cX
    cA
    wss
    #
    wa
    cX
    cA
    cpw
    #
    wcel
    #
    cA
    cX
    cdif
    #
    cvv
    wcel
    #
    cX
    cF
    cfv
    @4
    wceq
    @0
    @3
    @1
    cX
    cA
    cV
    elpw2g
    biimpar
    @0
    @5
    @1
    cA
    cX
    cV
    difexg
    adantr
    va
    cX
    cA
    va
    cv
    #
    cdif
    #
    @4
    @2
    cvv
    cF
    @6
    cX
    cA
    difeq2
    cF
    vx
    @2
    cA
    vx
    cv
    #
    cdif
    #
    cmpt
    va
    @2
    @7
    cmpt
    compss.a
    vx
    va
    @2
    @9
    @7
    @8
    @6
    cA
    difeq2
    cbvmptv
    eqtri
    fvmptg
    syl2anc
end
