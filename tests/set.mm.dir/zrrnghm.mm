include "crng.mm"
include "wcel.mm"
include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "crngh.mm"
include "eldifi.mm"
include "ringrng.mm"
include "syl.mm"
include "anim1i.mm"
include "ancoms.mm"
include "cgrp.mm"
include "c0g.mm"
include "csn.mm"
include "cabl.mm"
include "rngabl.mm"
include "ablgrp.mm"
include "adantr.mm"
include "ringgrp.mm"
include "adantl.mm"
include "eqid.mm"
include "0ringbas.mm"
include "c0snghm.mm"
include "syl3anc.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "eqidd.mm"
include "ring0cl.mm"
include "ad2antlr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvmptd.mm"
include "cbs.mm"
include "grpidcl.mm"
include "rnglz.mm"
include "mpdan.mm"
include "simpr.mm"
include "oveq12d.mm"
include "ringlz.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "wb.mm"
include "jca.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "2ralsng.mm"
include "mpbird.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "isrnghm.mm"
include "sylanbrc.mm"

theorem zrrnghm
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cT: class T
  let cH: class H
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume zrrhm.b: |- B = ( Base ` T )
  assume zrrhm.0: |- .0. = ( 0g ` S )
  assume zrrhm.h: |- H = ( x e. B |-> .0. )

  disjoint B x
  disjoint S x
  disjoint T x
  disjoint .0. x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint b c
  disjoint b x
  disjoint c x
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint k x
  assert |- ( ( S e. Rng /\ T e. ( Ring \ NzRing ) ) -> H e. ( T RngHomo S ) )

  proof
    cS
    crng
    wcel
    #
    cT
    crg
    cnzr
    cdif
    wcel
    #
    wa
    #
    cT
    crng
    wcel
    #
    @0
    wa
    #
    cH
    cT
    cS
    cghm
    co
    wcel
    #
    va
    cv
    #
    vc
    cv
    #
    cT
    cmulr
    cfv
    #
    co
    #
    cH
    cfv
    #
    @6
    cH
    cfv
    #
    @7
    cH
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    vc
    cB
    wral
    #
    va
    cB
    wral
    #
    wa
    cH
    cT
    cS
    crngh
    co
    wcel
    @1
    @0
    @4
    @1
    @3
    @0
    @1
    cT
    crg
    wcel
    #
    @3
    cT
    crg
    cnzr
    eldifi
    #
    cT
    ringrng
    syl
    anim1i
    ancoms
    @2
    @5
    @17
    @2
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    cB
    cT
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    @5
    @0
    @20
    @1
    @0
    cS
    cabl
    wcel
    @20
    cS
    rngabl
    cS
    ablgrp
    syl
    #
    adantr
    @1
    @21
    @0
    @1
    @18
    @21
    @19
    cT
    ringgrp
    syl
    adantl
    @1
    @24
    @0
    cB
    cT
    @22
    zrrhm.b
    @22
    eqid
    #
    0ringbas
    adantl
    #
    vx
    cB
    cS
    cT
    cH
    c.0
    @22
    zrrhm.b
    zrrhm.0
    zrrhm.h
    @26
    c0snghm
    syl3anc
    @2
    @24
    @17
    @27
    @2
    @24
    wa
    #
    @17
    @15
    vc
    @23
    wral
    #
    va
    @23
    wral
    #
    @28
    @30
    @22
    @22
    @8
    co
    #
    cH
    cfv
    #
    @22
    cH
    cfv
    #
    @33
    @13
    co
    #
    wceq
    #
    @28
    @33
    c.0
    wceq
    #
    @35
    @28
    vx
    @22
    c.0
    c.0
    cB
    cH
    cvv
    cH
    vx
    cB
    c.0
    cmpt
    wceq
    @28
    zrrhm.h
    a1i
    @28
    vx
    cv
    @22
    wceq
    wa
    c.0
    eqidd
    @1
    @22
    cB
    wcel
    #
    @0
    @24
    @1
    @18
    @37
    @19
    cB
    cT
    @22
    zrrhm.b
    @26
    ring0cl
    #
    syl
    ad2antlr
    c.0
    cvv
    wcel
    @28
    c.0
    cS
    c0g
    cfv
    cvv
    zrrhm.0
    cS
    c0g
    fvex
    eqeltri
    a1i
    fvmptd
    @28
    @36
    wa
    #
    c.0
    c.0
    @13
    co
    #
    c.0
    @34
    @32
    @28
    @40
    c.0
    wceq
    #
    @36
    @2
    @41
    @24
    @0
    @41
    @1
    @0
    c.0
    cS
    cbs
    cfv
    #
    wcel
    #
    @41
    @0
    @20
    @43
    @25
    @42
    cS
    c.0
    @42
    eqid
    #
    zrrhm.0
    grpidcl
    syl
    @42
    cS
    @13
    c.0
    c.0
    @44
    @13
    eqid
    #
    zrrhm.0
    rnglz
    mpdan
    adantr
    adantr
    adantr
    @39
    @33
    c.0
    @33
    c.0
    @13
    @28
    @36
    simpr
    #
    @46
    oveq12d
    @39
    @32
    @33
    c.0
    @39
    @31
    @22
    cH
    @28
    @31
    @22
    wceq
    #
    @36
    @1
    @47
    @0
    @24
    @1
    @18
    @47
    @19
    @18
    @37
    @47
    @38
    cB
    cT
    @8
    @22
    @22
    zrrhm.b
    @8
    eqid
    #
    @26
    ringlz
    mpdan
    syl
    ad2antlr
    adantr
    fveq2d
    @46
    eqtrd
    3eqtr4rd
    mpdan
    @28
    @37
    @37
    wa
    #
    @30
    @35
    wb
    @1
    @49
    @0
    @24
    @1
    @18
    @49
    @19
    @18
    @37
    @37
    @38
    @38
    jca
    syl
    ad2antlr
    @15
    @22
    @7
    @8
    co
    #
    cH
    cfv
    #
    @33
    @12
    @13
    co
    #
    wceq
    @35
    va
    vc
    @22
    @22
    cB
    cB
    @6
    @22
    wceq
    #
    @10
    @51
    @14
    @52
    @53
    @9
    @50
    cH
    @6
    @22
    @7
    @8
    oveq1
    fveq2d
    @53
    @11
    @33
    @12
    @13
    @6
    @22
    cH
    fveq2
    oveq1d
    eqeq12d
    @7
    @22
    wceq
    #
    @51
    @32
    @52
    @34
    @54
    @50
    @31
    cH
    @7
    @22
    @22
    @8
    oveq2
    fveq2d
    @54
    @12
    @33
    @33
    @13
    @7
    @22
    cH
    fveq2
    oveq2d
    eqeq12d
    2ralsng
    syl
    mpbird
    @24
    @17
    @30
    wb
    @2
    @16
    @29
    va
    cB
    @23
    @15
    vc
    cB
    @23
    raleq
    raleqbi1dv
    adantl
    mpbird
    mpdan
    jca
    va
    vc
    cB
    cT
    cS
    @8
    cH
    @13
    zrrhm.b
    @48
    @45
    isrnghm
    sylanbrc
end
