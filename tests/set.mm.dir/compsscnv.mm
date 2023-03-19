include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "ccnv.mm"
include "cnvopab.mm"
include "cmpt.mm"
include "difeq2.mm"
include "cbvmptv.mm"
include "df-mpt.mm"
include "3eqtri.mm"
include "cnveqi.mm"
include "compsscnvlem.mm"
include "impbii.mm"
include "opabbii.mm"
include "3eqtr4i.mm"

theorem compsscnv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cV: class V
  let cX: class X
  let cG: class G
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint A x
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
  disjoint V x
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- `' F = F

  proof
    vy
    cv
    #
    cA
    cpw
    #
    wcel
    vx
    cv
    #
    cA
    @0
    cdif
    #
    wceq
    wa
    #
    vy
    vx
    copab
    #
    ccnv
    @4
    vx
    vy
    copab
    #
    cF
    ccnv
    cF
    @4
    vy
    vx
    cnvopab
    cF
    @5
    cF
    vx
    @1
    cA
    @2
    cdif
    #
    cmpt
    #
    vy
    @1
    @3
    cmpt
    @5
    compss.a
    vx
    vy
    @1
    @7
    @3
    @2
    @0
    cA
    difeq2
    cbvmptv
    vy
    vx
    @1
    @3
    df-mpt
    3eqtri
    cnveqi
    @8
    @2
    @1
    wcel
    @0
    @7
    wceq
    wa
    #
    vx
    vy
    copab
    cF
    @6
    vx
    vy
    @1
    @7
    df-mpt
    compss.a
    @4
    @9
    vx
    vy
    @4
    @9
    vy
    vx
    cA
    compsscnvlem
    vx
    vy
    cA
    compsscnvlem
    impbii
    opabbii
    3eqtr4i
    3eqtr4i
end
