include "cmnd.mm"
include "wcel.mm"
include "cmgm.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cmgmhm.mm"
include "mndmgm.mm"
include "anim1i.mm"
include "3adant3.mm"
include "ancomd.mm"
include "csn.mm"
include "wex.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "eqid.mm"
include "mndidcl.mm"
include "adantr.mm"
include "fmptd.mm"
include "cmpt.mm"
include "a1i.mm"
include "weq.mm"
include "eqidd.mm"
include "vsnid.mm"
include "eleq2.mm"
include "mpbird.mm"
include "adantl.mm"
include "fvmptd.mm"
include "simpr.mm"
include "oveq12d.mm"
include "mndlid.mm"
include "mpdan.mm"
include "mgmcl.mm"
include "syl3anc.mm"
include "wi.mm"
include "elsni.mm"
include "syl6bi.mm"
include "mpd.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "3eqtrrd.mm"
include "id.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "vex.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "2ralsng.mm"
include "mp2an.mm"
include "syl6bb.mm"
include "jca.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"
include "ismgmhm.mm"
include "sylanbrc.mm"

theorem c0snmgmhm
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
  assert |- ( ( S e. Mnd /\ T e. Mgm /\ ( # ` B ) = 1 ) -> H e. ( T MgmHom S ) )

  proof
    cS
    cmnd
    wcel
    #
    cT
    cmgm
    wcel
    #
    cB
    chash
    cfv
    c1
    wceq
    #
    w3a
    #
    @1
    cS
    cmgm
    wcel
    #
    wa
    cB
    cS
    cbs
    cfv
    #
    cH
    wf
    #
    va
    cv
    #
    vc
    cv
    #
    cT
    cplusg
    cfv
    #
    co
    #
    cH
    cfv
    #
    @7
    cH
    cfv
    #
    @8
    cH
    cfv
    #
    cS
    cplusg
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
    #
    cH
    cT
    cS
    cmgmhm
    co
    wcel
    @3
    @4
    @1
    @0
    @1
    @4
    @1
    wa
    @2
    @0
    @4
    @1
    cS
    mndmgm
    anim1i
    3adant3
    ancomd
    @0
    @1
    @2
    @19
    @2
    cB
    vb
    cv
    #
    csn
    #
    wceq
    #
    vb
    wex
    #
    @0
    @1
    wa
    #
    @19
    cB
    cvv
    wcel
    @2
    @23
    wb
    cB
    cT
    cbs
    cfv
    cvv
    zrrhm.b
    cT
    cbs
    fvex
    eqeltri
    cB
    cvv
    vb
    hash1snb
    ax-mp
    @24
    @22
    @19
    vb
    @24
    @22
    @19
    @24
    @22
    wa
    #
    @6
    @18
    @25
    vx
    cB
    c.0
    @5
    cH
    @25
    c.0
    @5
    wcel
    #
    vx
    cv
    cB
    wcel
    @24
    @26
    @22
    @0
    @26
    @1
    @5
    cS
    c.0
    @5
    eqid
    #
    zrrhm.0
    mndidcl
    #
    adantr
    adantr
    #
    adantr
    zrrhm.h
    fmptd
    @25
    @18
    @20
    @20
    @9
    co
    #
    cH
    cfv
    #
    @20
    cH
    cfv
    #
    @32
    @14
    co
    #
    wceq
    #
    @25
    @32
    c.0
    wceq
    #
    @34
    @25
    vx
    @20
    c.0
    c.0
    cB
    cH
    @5
    cH
    vx
    cB
    c.0
    cmpt
    wceq
    @25
    zrrhm.h
    a1i
    @25
    vx
    vb
    weq
    wa
    c.0
    eqidd
    @22
    @20
    cB
    wcel
    #
    @24
    @22
    @36
    @20
    @21
    wcel
    #
    @37
    @22
    vb
    vsnid
    a1i
    cB
    @21
    @20
    eleq2
    mpbird
    adantl
    #
    @29
    fvmptd
    @25
    @35
    wa
    #
    @33
    c.0
    c.0
    @14
    co
    #
    c.0
    @31
    @39
    @32
    c.0
    @32
    c.0
    @14
    @25
    @35
    simpr
    #
    @41
    oveq12d
    @25
    @40
    c.0
    wceq
    #
    @35
    @24
    @42
    @22
    @0
    @42
    @1
    @0
    @26
    @42
    @28
    @5
    @14
    cS
    c.0
    c.0
    @27
    @14
    eqid
    #
    zrrhm.0
    mndlid
    mpdan
    adantr
    adantr
    adantr
    @39
    @31
    @32
    c.0
    @25
    @31
    @32
    wceq
    @35
    @25
    @30
    @20
    cH
    @25
    @36
    @30
    @20
    wceq
    #
    @38
    @25
    @36
    wa
    #
    @30
    cB
    wcel
    #
    @44
    @45
    @1
    @36
    @36
    @46
    @25
    @1
    @36
    @24
    @1
    @22
    @0
    @1
    simpr
    adantr
    adantr
    @25
    @36
    simpr
    #
    @47
    cB
    cT
    @20
    @20
    @9
    zrrhm.b
    @9
    eqid
    #
    mgmcl
    syl3anc
    @25
    @46
    @44
    wi
    #
    @36
    @22
    @49
    @24
    @22
    @46
    @30
    @21
    wcel
    @44
    cB
    @21
    @30
    eleq2
    @30
    @20
    elsni
    syl6bi
    adantl
    adantr
    mpd
    mpdan
    fveq2d
    adantr
    @41
    eqtr2d
    3eqtrrd
    mpdan
    @25
    @18
    @16
    vc
    @21
    wral
    #
    va
    @21
    wral
    #
    @34
    @22
    @18
    @51
    wb
    @24
    @22
    @17
    @50
    va
    cB
    @21
    @22
    id
    #
    @22
    @16
    vc
    cB
    @21
    @52
    raleqdv
    raleqbidv
    adantl
    @20
    cvv
    wcel
    #
    @53
    @51
    @34
    wb
    vb
    vex
    #
    @54
    @16
    @20
    @8
    @9
    co
    #
    cH
    cfv
    #
    @32
    @13
    @14
    co
    #
    wceq
    @34
    va
    vc
    @20
    @20
    cvv
    cvv
    va
    vb
    weq
    #
    @11
    @56
    @15
    @57
    @58
    @10
    @55
    cH
    @7
    @20
    @8
    @9
    oveq1
    fveq2d
    @58
    @12
    @32
    @13
    @14
    @7
    @20
    cH
    fveq2
    oveq1d
    eqeq12d
    vc
    vb
    weq
    #
    @56
    @31
    @57
    @33
    @59
    @55
    @30
    cH
    @8
    @20
    @20
    @9
    oveq2
    fveq2d
    @59
    @13
    @32
    @32
    @14
    @8
    @20
    cH
    fveq2
    oveq2d
    eqeq12d
    2ralsng
    mp2an
    syl6bb
    mpbird
    jca
    ex
    exlimdv
    syl5bi
    3impia
    va
    vc
    cB
    @5
    @9
    @14
    cT
    cS
    cH
    zrrhm.b
    @27
    @48
    @43
    ismgmhm
    sylanbrc
end
