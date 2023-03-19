include "crg.mm"
include "wcel.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "csn.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "cz.mm"
include "cmpt.mm"
include "cfv.mm"
include "cbs.mm"
include "wf.mm"
include "zringbas.mm"
include "eqid.mm"
include "rhmf.mm"
include "adantl.mm"
include "feqmptd.mm"
include "c1.mm"
include "cmg.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "1zzd.mm"
include "ghmmulg.mm"
include "syl3anc.mm"
include "ccnfld.mm"
include "cmul.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cnfldmulg.mm"
include "mpan2.mm"
include "1z.mm"
include "adantr.mm"
include "zringmulg.mm"
include "eqtr4d.mm"
include "zcn.mm"
include "mulid1d.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "zring1.mm"
include "rhm1.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "syl6eqr.mm"
include "velsn.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "mulgrhm.mm"
include "snssd.mm"
include "eqssd.mm"

theorem mulgrhm2
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vn: setvar n
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vf: setvar f
  assume mulgghm2.m: |- .x. = ( .g ` R )
  assume mulgghm2.f: |- F = ( n e. ZZ |-> ( n .x. .1. ) )
  assume mulgrhm.1: |- .1. = ( 1r ` R )

  disjoint R n
  disjoint .x. n
  disjoint .1. n
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f n
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint .1. x
  disjoint .1. y
  assert |- ( R e. Ring -> ( ZZring RingHom R ) = { F } )

  proof
    cR
    crg
    wcel
    #
    zring
    cR
    crh
    co
    #
    cF
    csn
    #
    @0
    vf
    @1
    @2
    @0
    vf
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    #
    @3
    cF
    wceq
    @5
    @6
    @3
    vn
    cz
    vn
    cv
    #
    c.1
    c.x
    co
    #
    cmpt
    #
    cF
    @6
    @3
    vn
    cz
    @7
    @3
    cfv
    #
    cmpt
    @9
    @6
    vn
    cz
    cR
    cbs
    cfv
    #
    @3
    @4
    cz
    @11
    @3
    wf
    @0
    cz
    @11
    zring
    cR
    @3
    zringbas
    @11
    eqid
    rhmf
    adantl
    feqmptd
    @6
    vn
    cz
    @10
    @8
    @6
    @7
    cz
    wcel
    #
    wa
    #
    @7
    c1
    zring
    cmg
    cfv
    #
    co
    #
    @3
    cfv
    #
    @7
    c1
    @3
    cfv
    #
    c.x
    co
    #
    @10
    @8
    @13
    @3
    zring
    cR
    cghm
    co
    wcel
    #
    @12
    c1
    cz
    wcel
    #
    @16
    @18
    wceq
    @4
    @19
    @0
    @12
    zring
    cR
    @3
    rhmghm
    ad2antlr
    @6
    @12
    simpr
    @13
    1zzd
    cz
    @14
    c.x
    @3
    zring
    cR
    @7
    c1
    zringbas
    @14
    eqid
    mulgghm2.m
    ghmmulg
    syl3anc
    @13
    @15
    @7
    @3
    @12
    @15
    @7
    wceq
    @6
    @12
    @7
    c1
    ccnfld
    cmg
    cfv
    co
    #
    @7
    c1
    cmul
    co
    #
    @15
    @7
    @12
    c1
    cc
    wcel
    @21
    @22
    wceq
    #
    ax-1cn
    @7
    c1
    cnfldmulg
    mpan2
    #
    @12
    @20
    @21
    @15
    wceq
    1z
    @12
    @20
    wa
    @21
    @22
    @15
    @12
    @23
    @20
    @24
    adantr
    @7
    c1
    zringmulg
    eqtr4d
    mpan2
    @12
    @7
    @7
    zcn
    mulid1d
    3eqtr3d
    adantl
    fveq2d
    @13
    @17
    c.1
    @7
    c.x
    @4
    @17
    c.1
    wceq
    @0
    @12
    zring
    cR
    c1
    @3
    c.1
    zring1
    mulgrhm.1
    rhm1
    ad2antlr
    oveq2d
    3eqtr3d
    mpteq2dva
    eqtrd
    mulgghm2.f
    syl6eqr
    vf
    cF
    velsn
    sylibr
    ex
    ssrdv
    @0
    cF
    @1
    cR
    c.x
    c.1
    vn
    cF
    mulgghm2.m
    mulgghm2.f
    mulgrhm.1
    mulgrhm
    snssd
    eqssd
end
