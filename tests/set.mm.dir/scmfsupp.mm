include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "funmpt.mm"
include "a1i.mm"
include "id.mm"
include "fsuppimpd.mm"
include "scmsuppfi.mm"
include "syl3an3.mm"
include "cvv.mm"
include "wb.mm"
include "mptexg.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "fvex.mm"
include "isfsupp.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem scmfsupp
  let vv: setvar v
  let cA: class A
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume scmsuppfi.s: |- S = ( Scalar ` M )
  assume scmsuppfi.r: |- R = ( Base ` S )

  disjoint A v
  disjoint M v
  disjoint R v
  disjoint V v
  disjoint k x
  assert |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\ A e. ( R ^m V ) /\ A finSupp ( 0g ` S ) ) -> ( v e. V |-> ( ( A ` v ) ( .s ` M ) v ) ) finSupp ( 0g ` M ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    cpw
    #
    wcel
    #
    wa
    #
    cA
    cR
    cV
    cmap
    co
    wcel
    #
    cA
    cS
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
    vv
    cv
    #
    cA
    cfv
    @8
    cM
    cvsca
    cfv
    co
    #
    cmpt
    #
    cM
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @10
    wfun
    #
    @10
    @11
    csupp
    co
    cfn
    wcel
    #
    @13
    @7
    vv
    cV
    @9
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
    @14
    @6
    cA
    @5
    @6
    id
    fsuppimpd
    vv
    cA
    cR
    cS
    cM
    cV
    scmsuppfi.s
    scmsuppfi.r
    scmsuppfi
    syl3an3
    @7
    @10
    cvv
    wcel
    #
    @11
    cvv
    wcel
    @12
    @13
    @14
    wa
    wb
    @3
    @4
    @15
    @6
    @2
    @15
    @0
    vv
    cV
    @9
    @1
    mptexg
    adantl
    3ad2ant1
    cM
    c0g
    fvex
    @10
    cvv
    cvv
    @11
    isfsupp
    sylancl
    mpbir2and
end
