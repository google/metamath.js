include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "cbs.mm"
include "csn.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "snex.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "mpt2exga.mm"
include "cop.mm"
include "lmodvsca.mm"
include "3syl.mm"
include "eqcomd.mm"
include "simprr.mm"
include "lmodsca.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eqid.mm"
include "ringidcl.mm"
include "eqeltrd.mm"
include "snidg.mm"
include "adantr.mm"
include "ovmpt2d.mm"

theorem lmod1lem5
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

  disjoint I x
  disjoint I y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint V x
  disjoint V y
  disjoint M x
  disjoint M y
  disjoint I r
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint V r
  disjoint I q
  disjoint R q
  disjoint V q
  disjoint q x
  disjoint q y
  disjoint k x
  assert |- ( ( I e. V /\ R e. Ring ) -> ( ( 1r ` ( Scalar ` M ) ) ( .s ` M ) I ) = I )

  proof
    cI
    cV
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    vx
    vy
    cM
    csca
    cfv
    #
    cur
    cfv
    #
    cI
    cR
    cbs
    cfv
    #
    cI
    csn
    #
    vy
    cv
    #
    cI
    cM
    cvsca
    cfv
    #
    @6
    @2
    vx
    vy
    @5
    @6
    @7
    cmpt2
    #
    @8
    @2
    @5
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    wa
    #
    @9
    cvv
    wcel
    @9
    @8
    wceq
    @12
    @2
    @10
    @11
    cR
    cbs
    fvex
    cI
    snex
    pm3.2i
    a1i
    vx
    vy
    @5
    @6
    @7
    cvv
    cvv
    mpt2exga
    @6
    cI
    cI
    cop
    cI
    cop
    csn
    #
    @9
    cR
    cM
    cvv
    lmod1.m
    lmodvsca
    3syl
    eqcomd
    @2
    vx
    cv
    @4
    wceq
    @7
    cI
    wceq
    simprr
    @2
    @4
    cR
    cur
    cfv
    #
    @5
    @2
    @3
    cR
    cur
    @2
    cR
    @3
    @1
    cR
    @3
    wceq
    @0
    @6
    @13
    @9
    cR
    cM
    crg
    lmod1.m
    lmodsca
    adantl
    eqcomd
    fveq2d
    @1
    @14
    @5
    wcel
    @0
    @5
    cR
    @14
    @5
    eqid
    @14
    eqid
    ringidcl
    adantl
    eqeltrd
    @0
    cI
    @6
    wcel
    @1
    cI
    cV
    snidg
    adantr
    #
    @15
    ovmpt2d
end
