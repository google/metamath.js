include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "csca.mm"
include "cmulr.mm"
include "csn.mm"
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
include "weq.mm"
include "simprr.mm"
include "simprl.mm"
include "snidg.mm"
include "ad2antrr.mm"
include "ovmpt2d.mm"
include "oveq2d.mm"
include "simplr.mm"
include "lmodsca.mm"
include "fveq2d.mm"
include "syl.mm"
include "oveqd.mm"
include "eqid.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "3eqtr4rd.mm"

theorem lmod1lem4
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
  disjoint M x
  disjoint M y
  disjoint q x
  disjoint q y
  disjoint k x
  assert |- ( ( ( I e. V /\ R e. Ring ) /\ ( q e. ( Base ` R ) /\ r e. ( Base ` R ) ) ) -> ( ( q ( .r ` ( Scalar ` M ) ) r ) ( .s ` M ) I ) = ( q ( .s ` M ) ( r ( .s ` M ) I ) ) )

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
    vq
    cv
    #
    cR
    cbs
    cfv
    #
    wcel
    #
    vr
    cv
    #
    @4
    wcel
    #
    wa
    #
    wa
    #
    @3
    cI
    cM
    cvsca
    cfv
    #
    co
    cI
    @3
    @6
    cI
    @10
    co
    #
    @10
    co
    @3
    @6
    cM
    csca
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    cI
    @10
    co
    @9
    vx
    vy
    @3
    cI
    @4
    cI
    csn
    #
    vy
    cv
    #
    cI
    @10
    @15
    @9
    vx
    vy
    @4
    @15
    @16
    cmpt2
    #
    @10
    @9
    @4
    cvv
    wcel
    #
    @15
    cvv
    wcel
    #
    wa
    #
    @17
    cvv
    wcel
    @17
    @10
    wceq
    @20
    @9
    @18
    @19
    cR
    cbs
    fvex
    cI
    snex
    pm3.2i
    a1i
    vx
    vy
    @4
    @15
    @16
    cvv
    cvv
    mpt2exga
    @15
    cI
    cI
    cop
    cI
    cop
    csn
    #
    @17
    cR
    cM
    cvv
    lmod1.m
    lmodvsca
    3syl
    eqcomd
    #
    @9
    vx
    vq
    weq
    @16
    cI
    wceq
    #
    simprr
    @2
    @5
    @7
    simprl
    #
    @0
    cI
    @15
    wcel
    @1
    @8
    cI
    cV
    snidg
    ad2antrr
    #
    @25
    ovmpt2d
    @9
    @11
    cI
    @3
    @10
    @9
    vx
    vy
    @6
    cI
    @4
    @15
    @16
    cI
    @10
    @15
    @22
    @9
    vx
    vr
    weq
    @23
    simprr
    @2
    @5
    @7
    simprr
    #
    @25
    @25
    ovmpt2d
    oveq2d
    @9
    vx
    vy
    @14
    cI
    @4
    @15
    @16
    cI
    @10
    @15
    @22
    @9
    vx
    cv
    @14
    wceq
    @23
    simprr
    @9
    @14
    @3
    @6
    cR
    cmulr
    cfv
    #
    co
    #
    @4
    @9
    @13
    @27
    @3
    @6
    @9
    @27
    @13
    @9
    @1
    @27
    @13
    wceq
    @0
    @1
    @8
    simplr
    #
    @1
    cR
    @12
    cmulr
    @15
    @21
    @17
    cR
    cM
    crg
    lmod1.m
    lmodsca
    fveq2d
    syl
    eqcomd
    oveqd
    @9
    @1
    @5
    @7
    @28
    @4
    wcel
    @29
    @24
    @26
    @4
    cR
    @27
    @3
    @6
    @4
    eqid
    @27
    eqid
    ringcl
    syl3anc
    eqeltrd
    @25
    @25
    ovmpt2d
    3eqtr4rd
end
