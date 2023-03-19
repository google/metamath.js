include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "w3a.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "funmpt2.mm"
include "a1i.mm"
include "suppmptcfin.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "cmpt.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "3ad2ant2.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "isfsupp.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem mptcfsupp
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let cM: class M
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vv: setvar v
  let vk: setvar k
  assume suppmptcfin.b: |- B = ( Base ` M )
  assume suppmptcfin.r: |- R = ( Scalar ` M )
  assume suppmptcfin.0: |- .0. = ( 0g ` R )
  assume suppmptcfin.1: |- .1. = ( 1r ` R )
  assume suppmptcfin.f: |- F = ( x e. V |-> if ( x = X , .1. , .0. ) )

  disjoint B x
  disjoint F x
  disjoint M x
  disjoint V x
  disjoint X x
  disjoint .1. x
  disjoint .0. x
  disjoint B v
  disjoint v x
  disjoint F v
  disjoint M v
  disjoint V v
  disjoint X v
  disjoint .1. v
  disjoint .0. v
  disjoint k x
  assert |- ( ( M e. LMod /\ V e. ~P B /\ X e. V ) -> F finSupp .0. )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    cpw
    #
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cF
    c.0
    cfsupp
    wbr
    #
    cF
    wfun
    #
    cF
    c.0
    csupp
    co
    cfn
    wcel
    #
    @6
    @4
    vx
    cV
    vx
    cv
    cX
    wceq
    c.1
    c.0
    cif
    #
    cF
    suppmptcfin.f
    funmpt2
    a1i
    vx
    cB
    cR
    c.1
    cF
    cM
    cV
    cX
    c.0
    suppmptcfin.b
    suppmptcfin.r
    suppmptcfin.0
    suppmptcfin.1
    suppmptcfin.f
    suppmptcfin
    @4
    cF
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    @5
    @6
    @7
    wa
    wb
    @2
    @0
    @9
    @3
    @2
    cF
    vx
    cV
    @8
    cmpt
    cvv
    suppmptcfin.f
    vx
    cV
    @8
    @1
    mptexg
    syl5eqel
    3ad2ant2
    c.0
    cR
    c0g
    cfv
    cvv
    suppmptcfin.0
    cR
    c0g
    fvex
    eqeltri
    cF
    cvv
    cvv
    c.0
    isfsupp
    sylancl
    mpbir2and
end
