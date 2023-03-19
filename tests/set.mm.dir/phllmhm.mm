include "cphl.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmhm.mm"
include "wral.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "cstv.mm"
include "w3a.mm"
include "clvec.mm"
include "csr.mm"
include "eqid.mm"
include "isphl.mm"
include "simp3bi.mm"
include "simp1.mm"
include "ralimi.mm"
include "syl.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem phllmhm
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.as: class .*
  let cK: class K
  let c.0: class .0.
  let c.x: class .x.
  let cZ: class Z
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume phllmhm.g: |- G = ( x e. V |-> ( x ., A ) )

  disjoint A x
  disjoint ., x
  disjoint V x
  disjoint W x
  disjoint x y
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint G y
  disjoint ., y
  disjoint .* x
  disjoint .* y
  disjoint F y
  disjoint K x
  disjoint .0. x
  disjoint .x. x
  disjoint V y
  disjoint W y
  disjoint Z x
  assert |- ( ( W e. PreHil /\ A e. V ) -> G e. ( W LMHom ( ringLMod ` F ) ) )

  proof
    cW
    cphl
    wcel
    #
    vx
    cV
    vx
    cv
    #
    vy
    cv
    #
    c.xi
    co
    #
    cmpt
    #
    cW
    cF
    crglmod
    cfv
    clmhm
    co
    #
    wcel
    #
    vy
    cV
    wral
    #
    cA
    cV
    wcel
    cG
    @5
    wcel
    #
    @0
    @6
    @2
    @2
    c.xi
    co
    cF
    c0g
    cfv
    #
    wceq
    @2
    cW
    c0g
    cfv
    #
    wceq
    wi
    #
    @2
    @1
    c.xi
    co
    cF
    cstv
    cfv
    #
    cfv
    @3
    wceq
    vx
    cV
    wral
    #
    w3a
    #
    vy
    cV
    wral
    #
    @7
    @0
    cW
    clvec
    wcel
    cF
    csr
    wcel
    @15
    vy
    vx
    cF
    c.xi
    @12
    cV
    cW
    @10
    @9
    phllmhm.v
    phlsrng.f
    phllmhm.h
    @10
    eqid
    @12
    eqid
    @9
    eqid
    isphl
    simp3bi
    @14
    @6
    vy
    cV
    @6
    @11
    @13
    simp1
    ralimi
    syl
    @6
    @8
    vy
    cA
    cV
    @2
    cA
    wceq
    #
    @4
    cG
    @5
    @16
    @4
    vx
    cV
    @1
    cA
    c.xi
    co
    #
    cmpt
    cG
    @16
    vx
    cV
    @3
    @17
    @2
    cA
    @1
    c.xi
    oveq2
    mpteq2dv
    phllmhm.g
    syl6eqr
    eleq1d
    rspccva
    sylan
end
