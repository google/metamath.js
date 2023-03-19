include "crg.mm"
include "wcel.mm"
include "cz.mm"
include "zring.mm"
include "cmul.mm"
include "cmulr.mm"
include "cfv.mm"
include "c1.mm"
include "zringbas.mm"
include "zring1.mm"
include "zringmulr.mm"
include "eqid.mm"
include "zringring.mm"
include "a1i.mm"
include "id.mm"
include "co.mm"
include "wceq.mm"
include "1z.mm"
include "cv.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "cbs.mm"
include "ringidcl.mm"
include "mulg1.mm"
include "syl.mm"
include "syl5eq.mm"
include "wa.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "adantr.mm"
include "simprr.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "ringlidm.mm"
include "syldan.mm"
include "oveq2d.mm"
include "simpl.mm"
include "simprl.mm"
include "mulgass2.mm"
include "syl13anc.mm"
include "mulgass.mm"
include "3eqtr4rd.mm"
include "zmulcl.mm"
include "adantl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "cghm.mm"
include "mulgghm2.mm"
include "syl2anc.mm"
include "isrhm2d.mm"

theorem mulgrhm
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
  assert |- ( R e. Ring -> F e. ( ZZring RingHom R ) )

  proof
    cR
    crg
    wcel
    #
    vx
    vy
    cz
    zring
    cR
    cmul
    cR
    cmulr
    cfv
    #
    c1
    cF
    c.1
    zringbas
    zring1
    mulgrhm.1
    zringmulr
    @1
    eqid
    #
    zring
    crg
    wcel
    @0
    zringring
    a1i
    @0
    id
    @0
    c1
    cF
    cfv
    #
    c1
    c.1
    c.x
    co
    #
    c.1
    c1
    cz
    wcel
    @3
    @4
    wceq
    1z
    vn
    c1
    vn
    cv
    #
    c.1
    c.x
    co
    #
    @4
    cz
    cF
    @5
    c1
    c.1
    c.x
    oveq1
    mulgghm2.f
    c1
    c.1
    c.x
    ovex
    fvmpt
    ax-mp
    @0
    c.1
    cR
    cbs
    cfv
    #
    wcel
    #
    @4
    c.1
    wceq
    @7
    cR
    c.1
    @7
    eqid
    #
    mulgrhm.1
    ringidcl
    #
    @7
    c.x
    cR
    c.1
    @9
    mulgghm2.m
    mulg1
    syl
    syl5eq
    @0
    vx
    cv
    #
    cz
    wcel
    #
    vy
    cv
    #
    cz
    wcel
    #
    wa
    #
    wa
    #
    @11
    @13
    cmul
    co
    #
    c.1
    c.x
    co
    #
    @11
    c.1
    c.x
    co
    #
    @13
    c.1
    c.x
    co
    #
    @1
    co
    #
    @17
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    @1
    co
    #
    @16
    @11
    c.1
    @20
    @1
    co
    #
    c.x
    co
    #
    @11
    @20
    c.x
    co
    #
    @21
    @18
    @16
    @26
    @20
    @11
    c.x
    @0
    @15
    @20
    @7
    wcel
    #
    @26
    @20
    wceq
    @16
    cR
    cgrp
    wcel
    #
    @14
    @8
    @29
    @0
    @30
    @15
    cR
    ringgrp
    #
    adantr
    #
    @0
    @12
    @14
    simprr
    #
    @0
    @8
    @15
    @10
    adantr
    #
    @7
    c.x
    cR
    @13
    c.1
    @9
    mulgghm2.m
    mulgcl
    syl3anc
    #
    @7
    cR
    @1
    c.1
    @20
    @9
    @2
    mulgrhm.1
    ringlidm
    syldan
    oveq2d
    @16
    @0
    @12
    @8
    @29
    @21
    @27
    wceq
    @0
    @15
    simpl
    @0
    @12
    @14
    simprl
    #
    @34
    @35
    @7
    cR
    c.x
    @1
    @11
    c.1
    @20
    @9
    mulgghm2.m
    @2
    mulgass2
    syl13anc
    @16
    @30
    @12
    @14
    @8
    @18
    @28
    wceq
    @32
    @36
    @33
    @34
    @7
    c.x
    cR
    @11
    @13
    c.1
    @9
    mulgghm2.m
    mulgass
    syl13anc
    3eqtr4rd
    @16
    @17
    cz
    wcel
    #
    @22
    @18
    wceq
    @15
    @37
    @0
    @11
    @13
    zmulcl
    adantl
    vn
    @17
    @6
    @18
    cz
    cF
    @5
    @17
    c.1
    c.x
    oveq1
    mulgghm2.f
    @17
    c.1
    c.x
    ovex
    fvmpt
    syl
    @15
    @25
    @21
    wceq
    @0
    @12
    @14
    @23
    @19
    @24
    @20
    @1
    vn
    @11
    @6
    @19
    cz
    cF
    @5
    @11
    c.1
    c.x
    oveq1
    mulgghm2.f
    @11
    c.1
    c.x
    ovex
    fvmpt
    vn
    @13
    @6
    @20
    cz
    cF
    @5
    @13
    c.1
    c.x
    oveq1
    mulgghm2.f
    @13
    c.1
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    @0
    @30
    @8
    cF
    zring
    cR
    cghm
    co
    wcel
    @31
    @10
    @7
    cR
    c.x
    c.1
    vn
    cF
    mulgghm2.m
    mulgghm2.f
    @9
    mulgghm2
    syl2anc
    isrhm2d
end
