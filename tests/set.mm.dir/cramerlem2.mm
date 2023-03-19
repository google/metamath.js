include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cmatrepV.mm"
include "cmpt.mm"
include "wi.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "simplr.mm"
include "simpr.mm"
include "cramerlem1.mm"
include "syl113anc.mm"
include "ex.mm"
include "ralrimiva.mm"

theorem cramerlem2
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let cZ: class Z
  assume cramer.a: |- A = ( N Mat R )
  assume cramer.b: |- B = ( Base ` A )
  assume cramer.v: |- V = ( ( Base ` R ) ^m N )
  assume cramer.d: |- D = ( N maDet R )
  assume cramer.x: |- .x. = ( R maVecMul <. N , N >. )
  assume cramer.q: |- ./ = ( /r ` R )

  disjoint B i
  disjoint D i
  disjoint N i
  disjoint R i
  disjoint V i
  disjoint X i
  disjoint Y i
  disjoint .x. i
  disjoint ./ i
  disjoint B z
  disjoint D z
  disjoint N z
  disjoint i z
  disjoint R z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint A a
  disjoint B a
  disjoint a i
  disjoint D a
  disjoint N a
  disjoint R a
  disjoint V a
  disjoint X a
  disjoint Y a
  disjoint Z a
  disjoint Z i
  disjoint .x. a
  disjoint ./ a
  assert |- ( ( R e. CRing /\ ( X e. B /\ Y e. V ) /\ ( D ` X ) e. ( Unit ` R ) ) -> A. z e. V ( ( X .x. z ) = Y -> z = ( i e. N |-> ( ( D ` ( ( X ( N matRepV R ) Y ) ` i ) ) ./ ( D ` X ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cX
    cB
    wcel
    cY
    cV
    wcel
    wa
    #
    cX
    cD
    cfv
    #
    cR
    cui
    cfv
    wcel
    #
    w3a
    #
    cX
    vz
    cv
    #
    c.x
    co
    cY
    wceq
    #
    @5
    vi
    cN
    vi
    cv
    cX
    cY
    cN
    cR
    cmatrepV
    co
    co
    cfv
    cD
    cfv
    @2
    c.dv
    co
    cmpt
    wceq
    #
    wi
    vz
    cV
    @4
    @5
    cV
    wcel
    #
    wa
    #
    @6
    @7
    @9
    @6
    wa
    @0
    @1
    @3
    @8
    @6
    @7
    @0
    @1
    @3
    @8
    @6
    simpll1
    @0
    @1
    @3
    @8
    @6
    simpll2
    @0
    @1
    @3
    @8
    @6
    simpll3
    @4
    @8
    @6
    simplr
    @9
    @6
    simpr
    cA
    cB
    cD
    c.dv
    cR
    c.x
    vi
    cN
    cV
    cX
    cY
    @5
    cramer.a
    cramer.b
    cramer.v
    cramer.d
    cramer.x
    cramer.q
    cramerlem1
    syl113anc
    ex
    ralrimiva
end
