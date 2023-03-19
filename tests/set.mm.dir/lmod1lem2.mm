include "wcel.mm"
include "crg.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "csn.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "wa.mm"
include "fvex.mm"
include "snex.mm"
include "pm3.2i.mm"
include "mpt2exga.mm"
include "mp1i.mm"
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
include "lmodplusg.mm"
include "oveqd.mm"
include "df-ov.mm"
include "opex.mm"
include "simp1.mm"
include "fvsng.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "a1i.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem lmod1lem2
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
  assert |- ( ( I e. V /\ R e. Ring /\ r e. ( Base ` R ) ) -> ( r ( .s ` M ) ( I ( +g ` M ) I ) ) = ( ( r ( .s ` M ) I ) ( +g ` M ) ( r ( .s ` M ) I ) ) )

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
    #
    cI
    @2
    cI
    cI
    cM
    cplusg
    cfv
    #
    co
    #
    @6
    co
    @7
    @7
    @8
    co
    #
    @5
    vx
    vy
    @2
    cI
    @3
    cI
    csn
    #
    vy
    cv
    #
    cI
    @6
    @11
    @5
    vx
    vy
    @3
    @11
    @12
    cmpt2
    #
    @6
    @5
    @13
    cvv
    wcel
    #
    @13
    @6
    wceq
    #
    @3
    cvv
    wcel
    #
    @11
    cvv
    wcel
    #
    wa
    @14
    @5
    @16
    @17
    cR
    cbs
    fvex
    #
    cI
    snex
    #
    pm3.2i
    vx
    vy
    @3
    @11
    @12
    cvv
    cvv
    mpt2exga
    #
    mp1i
    @11
    cI
    cI
    cop
    #
    cI
    cop
    #
    csn
    #
    @13
    cR
    cM
    cvv
    lmod1.m
    lmodvsca
    #
    syl
    eqcomd
    @5
    vx
    vr
    weq
    @12
    cI
    wceq
    simprr
    #
    @0
    @1
    @4
    simp3
    #
    @0
    @1
    cI
    @11
    wcel
    @4
    cI
    cV
    snidg
    3ad2ant1
    #
    @27
    ovmpt2d
    @5
    @9
    cI
    @2
    @6
    @5
    @9
    cI
    cI
    @23
    co
    #
    cI
    @5
    @8
    @23
    cI
    cI
    @5
    @23
    @8
    @23
    cvv
    wcel
    @23
    @8
    wceq
    @5
    @22
    snex
    @11
    @23
    @13
    cR
    cM
    cvv
    lmod1.m
    lmodplusg
    mp1i
    eqcomd
    oveqd
    @5
    @28
    @21
    @23
    cfv
    #
    cI
    cI
    cI
    @23
    df-ov
    @5
    @21
    cvv
    wcel
    @0
    @29
    cI
    wceq
    cI
    cI
    opex
    @0
    @1
    @4
    simp1
    @21
    cI
    cvv
    cV
    fvsng
    sylancr
    syl5eq
    eqtrd
    #
    oveq2d
    @5
    @10
    @9
    cI
    @5
    @7
    cI
    @7
    cI
    @8
    @5
    vx
    vy
    @2
    cI
    @3
    @11
    @12
    cI
    @6
    @11
    @5
    @13
    @6
    @5
    @14
    @15
    @5
    @16
    @17
    @14
    @18
    @17
    @5
    @19
    a1i
    @20
    sylancr
    @24
    syl
    eqcomd
    @25
    @26
    @27
    @27
    ovmpt2d
    #
    @31
    oveq12d
    @30
    eqtrd
    3eqtr4d
end
