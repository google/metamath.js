include "ccrg.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "w3a.mm"
include "cv.mm"
include "cmatrepV.mm"
include "co.mm"
include "cmpt.mm"
include "wceq.mm"
include "wi.mm"
include "pm3.22.mm"
include "cramerlem3.mm"
include "syl3an1.mm"
include "simpl1l.mm"
include "simpl2.mm"
include "simpl3.mm"
include "crg.mm"
include "crngring.mm"
include "anim1i.mm"
include "ancomd.mm"
include "3adant3.mm"
include "slesolvec.mm"
include "imp.mm"
include "sylan.mm"
include "simpr.mm"
include "cramerlem1.mm"
include "syl113anc.mm"
include "ex.mm"
include "impbid.mm"

theorem cramer
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
  let cZ: class Z
  let va: setvar a
  let vz: setvar z
  let vv: setvar v
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
  disjoint Z i
  disjoint .x. i
  disjoint ./ i
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
  disjoint .x. a
  disjoint ./ a
  disjoint B z
  disjoint D z
  disjoint N z
  disjoint i z
  disjoint R z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint A v
  disjoint A z
  disjoint v z
  disjoint B v
  disjoint D v
  disjoint N v
  disjoint i v
  disjoint R v
  disjoint V v
  disjoint X v
  disjoint Y v
  disjoint .x. v
  disjoint .x. z
  disjoint ./ v
  disjoint ./ z
  assert |- ( ( ( R e. CRing /\ N =/= (/) ) /\ ( X e. B /\ Y e. V ) /\ ( D ` X ) e. ( Unit ` R ) ) -> ( Z = ( i e. N |-> ( ( D ` ( ( X ( N matRepV R ) Y ) ` i ) ) ./ ( D ` X ) ) ) <-> ( X .x. Z ) = Y ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    c0
    wne
    #
    wa
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
    cZ
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
    @4
    c.dv
    co
    cmpt
    wceq
    #
    cX
    cZ
    c.x
    co
    cY
    wceq
    #
    @2
    @1
    @0
    wa
    @3
    @5
    @7
    @8
    wi
    @0
    @1
    pm3.22
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
    cZ
    cramer.a
    cramer.b
    cramer.v
    cramer.d
    cramer.x
    cramer.q
    cramerlem3
    syl3an1
    @6
    @8
    @7
    @6
    @8
    wa
    @0
    @3
    @5
    cZ
    cV
    wcel
    #
    @8
    @7
    @0
    @1
    @3
    @5
    @8
    simpl1l
    @2
    @3
    @5
    @8
    simpl2
    @2
    @3
    @5
    @8
    simpl3
    @6
    @1
    cR
    crg
    wcel
    #
    wa
    #
    @3
    wa
    #
    @8
    @9
    @2
    @3
    @12
    @5
    @2
    @11
    @3
    @2
    @10
    @1
    @0
    @10
    @1
    cR
    crngring
    anim1i
    ancomd
    anim1i
    3adant3
    @12
    @8
    @9
    cA
    cB
    cR
    c.x
    cN
    cV
    cX
    cY
    cZ
    cramer.a
    cramer.b
    cramer.v
    cramer.x
    slesolvec
    imp
    sylan
    @6
    @8
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
    cZ
    cramer.a
    cramer.b
    cramer.v
    cramer.d
    cramer.x
    cramer.q
    cramerlem1
    syl113anc
    ex
    impbid
end
