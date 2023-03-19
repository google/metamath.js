include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "funmpt.mm"
include "a1i.mm"
include "id.mm"
include "fsuppimpd.mm"
include "rmsuppfi.mm"
include "syl3an3.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "mptexg.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "fvex.mm"
include "isfsupp.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem rmfsupp
  let vv: setvar v
  let cA: class A
  let cC: class C
  let cR: class R
  let cM: class M
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume rmsuppfi.r: |- R = ( Base ` M )

  disjoint A v
  disjoint C v
  disjoint M v
  disjoint R v
  disjoint X v
  disjoint V v
  disjoint k x
  assert |- ( ( ( M e. Ring /\ V e. X /\ C e. R ) /\ A e. ( R ^m V ) /\ A finSupp ( 0g ` M ) ) -> ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) finSupp ( 0g ` M ) )

  proof
    cM
    crg
    wcel
    #
    cV
    cX
    wcel
    #
    cC
    cR
    wcel
    #
    w3a
    #
    cA
    cR
    cV
    cmap
    co
    wcel
    #
    cA
    cM
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    w3a
    #
    vv
    cV
    cC
    vv
    cv
    cA
    cfv
    cM
    cmulr
    cfv
    co
    #
    cmpt
    #
    @5
    cfsupp
    wbr
    #
    @9
    wfun
    #
    @9
    @5
    csupp
    co
    cfn
    wcel
    #
    @11
    @7
    vv
    cV
    @8
    funmpt
    a1i
    @6
    @3
    @4
    cA
    @5
    csupp
    co
    cfn
    wcel
    @12
    @6
    cA
    @5
    @6
    id
    fsuppimpd
    vv
    cA
    cC
    cR
    cM
    cV
    cX
    rmsuppfi.r
    rmsuppfi
    syl3an3
    @7
    @9
    cvv
    wcel
    #
    @5
    cvv
    wcel
    @10
    @11
    @12
    wa
    wb
    @3
    @4
    @13
    @6
    @1
    @0
    @13
    @2
    vv
    cV
    @8
    cX
    mptexg
    3ad2ant2
    3ad2ant1
    cM
    c0g
    fvex
    @9
    cvv
    cvv
    @5
    isfsupp
    sylancl
    mpbir2and
end
