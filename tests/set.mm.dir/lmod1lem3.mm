include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "cplusg.mm"
include "co.mm"
include "csn.mm"
include "cmpt2.mm"
include "cvsca.mm"
include "eqidd.mm"
include "wceq.mm"
include "simprr.mm"
include "simplr.mm"
include "cop.mm"
include "lmodsca.mm"
include "fveq2d.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "simprl.mm"
include "eqid.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "snidg.mm"
include "adantr.mm"
include "simpl.mm"
include "ovmpt2d.mm"
include "cvv.mm"
include "fvex.mm"
include "snex.mm"
include "pm3.2i.mm"
include "mpt2exga.mm"
include "mp1i.mm"
include "lmodvsca.mm"
include "weq.mm"
include "oveq12d.mm"
include "lmodplusg.mm"
include "df-ov.mm"
include "opex.mm"
include "jctil.mm"
include "fvsng.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"

theorem lmod1lem3
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
  assert |- ( ( ( I e. V /\ R e. Ring ) /\ ( q e. ( Base ` R ) /\ r e. ( Base ` R ) ) ) -> ( ( q ( +g ` ( Scalar ` M ) ) r ) ( .s ` M ) I ) = ( ( q ( .s ` M ) I ) ( +g ` M ) ( r ( .s ` M ) I ) ) )

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
    @6
    cM
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cI
    vx
    vy
    @4
    cI
    csn
    #
    vy
    cv
    #
    cmpt2
    #
    co
    cI
    @12
    cI
    cM
    cvsca
    cfv
    #
    co
    @3
    cI
    @16
    co
    #
    @6
    cI
    @16
    co
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @9
    vx
    vy
    @12
    cI
    @4
    @13
    @14
    cI
    @15
    cV
    @9
    @15
    eqidd
    @9
    vx
    cv
    @12
    wceq
    @14
    cI
    wceq
    #
    simprr
    @9
    @12
    @3
    @6
    cR
    cplusg
    cfv
    #
    co
    #
    @4
    @9
    @11
    @22
    @3
    @6
    @9
    @22
    @11
    @9
    @1
    @22
    @11
    wceq
    @0
    @1
    @8
    simplr
    #
    @1
    cR
    @10
    cplusg
    @13
    cI
    cI
    cop
    #
    cI
    cop
    #
    csn
    #
    @15
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
    @23
    @4
    wcel
    @24
    @2
    @5
    @7
    simprl
    #
    @2
    @5
    @7
    simprr
    #
    @4
    @22
    cR
    @3
    @6
    @4
    eqid
    @22
    eqid
    ringacl
    syl3anc
    eqeltrd
    @2
    cI
    @13
    wcel
    #
    @8
    @0
    @30
    @1
    cI
    cV
    snidg
    adantr
    adantr
    #
    @2
    @0
    @8
    @0
    @1
    simpl
    #
    adantr
    ovmpt2d
    @9
    @16
    @15
    @12
    cI
    @9
    @15
    @16
    @9
    @15
    cvv
    wcel
    #
    @15
    @16
    wceq
    @4
    cvv
    wcel
    #
    @13
    cvv
    wcel
    #
    wa
    @33
    @9
    @34
    @35
    cR
    cbs
    fvex
    cI
    snex
    pm3.2i
    vx
    vy
    @4
    @13
    @14
    cvv
    cvv
    mpt2exga
    mp1i
    @13
    @27
    @15
    cR
    cM
    cvv
    lmod1.m
    lmodvsca
    syl
    eqcomd
    #
    oveqd
    @9
    @20
    cI
    cI
    @19
    co
    cI
    cI
    @27
    co
    #
    cI
    @9
    @17
    cI
    @18
    cI
    @19
    @9
    vx
    vy
    @3
    cI
    @4
    @13
    @14
    cI
    @16
    @13
    @36
    @9
    vx
    vq
    weq
    @21
    simprr
    @28
    @31
    @31
    ovmpt2d
    @9
    vx
    vy
    @6
    cI
    @4
    @13
    @14
    cI
    @16
    @13
    @36
    @9
    vx
    vr
    weq
    @21
    simprr
    @29
    @31
    @31
    ovmpt2d
    oveq12d
    @9
    @19
    @27
    cI
    cI
    @9
    @27
    @19
    @27
    cvv
    wcel
    @27
    @19
    wceq
    @9
    @26
    snex
    @13
    @27
    @15
    cR
    cM
    cvv
    lmod1.m
    lmodplusg
    mp1i
    eqcomd
    oveqd
    @9
    @37
    @25
    @27
    cfv
    #
    cI
    cI
    cI
    @27
    df-ov
    @9
    @25
    cvv
    wcel
    #
    @0
    wa
    #
    @38
    cI
    wceq
    @2
    @40
    @8
    @2
    @0
    @39
    @32
    cI
    cI
    opex
    jctil
    adantr
    @25
    cI
    cvv
    cV
    fvsng
    syl
    syl5eq
    3eqtrd
    3eqtr4d
end
