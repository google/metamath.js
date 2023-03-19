include "wcel.mm"
include "crg.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "snex.mm"
include "a1i.mm"
include "mpt2exga.mm"
include "sylancr.mm"
include "cop.mm"
include "lmodvsca.mm"
include "syl.mm"
include "eqcomd.mm"
include "weq.mm"
include "simprr.mm"
include "simp3.mm"
include "snidg.mm"
include "3ad2ant1.mm"
include "ovmpt2d.mm"
include "eqeltrd.mm"

theorem lmod1lem1
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cI: class I
  let cM: class M
  let cV: class V
  let vr: setvar r
  let vq: setvar q
  let vk: setvar k
  assume lmod1.m: |- M = ( { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. , <. ( Scalar ` ndx ) , R >. } u. { <. ( .s ` ndx ) , ( x e. ( Base ` R ) , y e. { I } |-> y ) >. } )

  disjoint I r
  disjoint I x
  disjoint I y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint V r
  disjoint V x
  disjoint V y
  disjoint I q
  disjoint R q
  disjoint V q
  disjoint k x
  assert |- ( ( I e. V /\ R e. Ring /\ r e. ( Base ` R ) ) -> ( r ( .s ` M ) I ) e. { I } )

  proof
    cI
    cV
    wcel
    #
    cR
    crg
    wcel
    #
    vr
    cv
    #
    cR
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    @2
    cI
    cM
    cvsca
    cfv
    #
    co
    cI
    cI
    csn
    #
    @5
    vx
    vy
    @2
    cI
    @3
    @7
    vy
    cv
    #
    cI
    @6
    @7
    @5
    vx
    vy
    @3
    @7
    @8
    cmpt2
    #
    @6
    @5
    @9
    cvv
    wcel
    #
    @9
    @6
    wceq
    @5
    @3
    cvv
    wcel
    @7
    cvv
    wcel
    #
    @10
    cR
    cbs
    fvex
    @11
    @5
    cI
    snex
    a1i
    vx
    vy
    @3
    @7
    @8
    cvv
    cvv
    mpt2exga
    sylancr
    @7
    cI
    cI
    cop
    cI
    cop
    csn
    @9
    cR
    cM
    cvv
    lmod1.m
    lmodvsca
    syl
    eqcomd
    @5
    vx
    vr
    weq
    @8
    cI
    wceq
    simprr
    @0
    @1
    @4
    simp3
    @0
    @1
    cI
    @7
    wcel
    @4
    cI
    cV
    snidg
    3ad2ant1
    #
    @12
    ovmpt2d
    @12
    eqeltrd
end
