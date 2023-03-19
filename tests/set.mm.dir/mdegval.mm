include "cv.mm"
include "csupp.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "supeq1d.mm"
include "mdegfval.mm"
include "xrltso.mm"
include "supex.mm"
include "fvmpt.mm"

theorem mdegval
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vh: setvar h
  let vm: setvar m
  let cF: class F
  let cH: class H
  let cI: class I
  let c.0: class .0.
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  assume mdegval.d: |- D = ( I mDeg R )
  assume mdegval.p: |- P = ( I mPoly R )
  assume mdegval.b: |- B = ( Base ` P )
  assume mdegval.z: |- .0. = ( 0g ` R )
  assume mdegval.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume mdegval.h: |- H = ( h e. A |-> ( CCfld gsum h ) )

  disjoint A h
  disjoint I m
  disjoint .0. h
  disjoint B f
  disjoint B i
  disjoint B r
  disjoint f i
  disjoint f r
  disjoint i r
  disjoint I f
  disjoint I i
  disjoint I r
  disjoint R f
  disjoint R i
  disjoint R r
  disjoint .0. i
  disjoint .0. r
  disjoint h i
  disjoint h r
  disjoint f h
  disjoint F f
  disjoint H f
  disjoint .0. f
  assert |- ( F e. B -> ( D ` F ) = sup ( ( H " ( F supp .0. ) ) , RR* , < ) )

  proof
    vf
    cF
    cH
    vf
    cv
    #
    c.0
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    cH
    cF
    c.0
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    cB
    cD
    @0
    cF
    wceq
    #
    cxr
    @2
    @4
    clt
    @5
    @1
    @3
    cH
    @0
    cF
    c.0
    csupp
    oveq1
    imaeq2d
    supeq1d
    cA
    cB
    cD
    cP
    cR
    vf
    vh
    vm
    cH
    cI
    c.0
    mdegval.d
    mdegval.p
    mdegval.b
    mdegval.z
    mdegval.a
    mdegval.h
    mdegfval
    cxr
    @4
    clt
    xrltso
    supex
    fvmpt
end
