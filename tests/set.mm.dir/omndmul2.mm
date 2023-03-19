include "comnd.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "co.mm"
include "df-3an.mm"
include "anass.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "simplr.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "cpo.mm"
include "ctos.mm"
include "omndtos.mm"
include "tospos.mm"
include "syl.mm"
include "cmnd.mm"
include "omndmnd.mm"
include "mndidcl.mm"
include "posref.mm"
include "syl2anc.mm"
include "ad3antrrr.mm"
include "mulg0.mm"
include "ad3antlr.mm"
include "breqtrrd.mm"
include "ad5antr.mm"
include "simp-5r.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "simpr32.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "3anassrs.mm"
include "3jca.mm"
include "simpr.mm"
include "cplusg.mm"
include "cfv.mm"
include "simp-4l.mm"
include "ad4antr.mm"
include "simp-4r.mm"
include "eqid.mm"
include "omndadd.mm"
include "syl131anc.mm"
include "mndlid.mm"
include "mulgnn0dir.mm"
include "syl13anc.mm"
include "1cnd.mm"
include "simpr3.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "mulg1.mm"
include "3eqtr3rd.mm"
include "3brtr3d.mm"
include "adantr.mm"
include "postr.mm"
include "imp.mm"
include "syl22anc.mm"
include "nn0indd.mm"
include "mpdan.mm"
include "sylbi.mm"

theorem omndmul2
  let cB: class B
  let c.x: class .x.
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let cY: class Y
  let wph: wff ph
  assume omndmul.0: |- B = ( Base ` M )
  assume omndmul.1: |- .<_ = ( le ` M )
  assume omndmul2.2: |- .x. = ( .g ` M )
  assume omndmul2.3: |- .0. = ( 0g ` M )


  assert |- ( ( M e. oMnd /\ ( X e. B /\ N e. NN0 ) /\ .0. .<_ X ) -> .0. .<_ ( N .x. X ) )

  proof
    cM
    comnd
    wcel
    #
    cX
    cB
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    c.0
    cX
    c.le
    wbr
    #
    w3a
    #
    @0
    @1
    wa
    #
    @2
    wa
    #
    @4
    wa
    #
    c.0
    cN
    cX
    c.x
    co
    #
    c.le
    wbr
    #
    @5
    @0
    @3
    wa
    #
    @4
    wa
    @8
    @0
    @3
    @4
    df-3an
    @7
    @11
    @4
    @0
    @1
    @2
    anass
    anbi1i
    bitr4i
    @8
    @2
    @10
    @6
    @2
    @4
    simplr
    @8
    c.0
    vm
    cv
    #
    cX
    c.x
    co
    #
    c.le
    wbr
    c.0
    cc0
    cX
    c.x
    co
    #
    c.le
    wbr
    c.0
    vn
    cv
    #
    cX
    c.x
    co
    #
    c.le
    wbr
    #
    c.0
    @15
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    c.le
    wbr
    #
    @10
    vm
    vn
    cN
    @12
    cc0
    wceq
    @13
    @14
    c.0
    c.le
    @12
    cc0
    cX
    c.x
    oveq1
    breq2d
    @12
    @15
    wceq
    @13
    @16
    c.0
    c.le
    @12
    @15
    cX
    c.x
    oveq1
    breq2d
    @12
    @18
    wceq
    @13
    @19
    c.0
    c.le
    @12
    @18
    cX
    c.x
    oveq1
    breq2d
    @12
    cN
    wceq
    @13
    @9
    c.0
    c.le
    @12
    cN
    cX
    c.x
    oveq1
    breq2d
    @8
    c.0
    c.0
    @14
    c.le
    @0
    c.0
    c.0
    c.le
    wbr
    #
    @1
    @2
    @4
    @0
    cM
    cpo
    wcel
    #
    c.0
    cB
    wcel
    #
    @21
    @0
    cM
    ctos
    wcel
    @22
    cM
    omndtos
    cM
    tospos
    syl
    #
    @0
    cM
    cmnd
    wcel
    #
    @23
    cM
    omndmnd
    #
    cB
    cM
    c.0
    omndmul.0
    omndmul2.3
    mndidcl
    #
    syl
    cB
    cM
    c.le
    c.0
    omndmul.0
    omndmul.1
    posref
    syl2anc
    ad3antrrr
    @1
    @14
    c.0
    wceq
    @0
    @2
    @4
    cB
    c.x
    cM
    cX
    c.0
    omndmul.0
    omndmul2.3
    omndmul2.2
    mulg0
    ad3antlr
    breqtrrd
    @8
    @15
    cn0
    wcel
    #
    wa
    #
    @17
    wa
    #
    @22
    @23
    @16
    cB
    wcel
    #
    @19
    cB
    wcel
    #
    w3a
    #
    @17
    @16
    @19
    c.le
    wbr
    #
    @20
    @0
    @22
    @1
    @2
    @4
    @28
    @17
    @24
    ad5antr
    @30
    @23
    @31
    @32
    @30
    @25
    @23
    @0
    @25
    @1
    @2
    @4
    @28
    @17
    @26
    ad5antr
    #
    @27
    syl
    @30
    @25
    @28
    @1
    @31
    @35
    @8
    @28
    @17
    simplr
    @0
    @1
    @2
    @4
    @28
    @17
    simp-5r
    #
    cB
    c.x
    cM
    @15
    cX
    omndmul.0
    omndmul2.2
    mulgnn0cl
    #
    syl3anc
    @30
    @25
    @18
    cn0
    wcel
    #
    @1
    @32
    @35
    @7
    @4
    @28
    @17
    @38
    @0
    @1
    @2
    @4
    @28
    @17
    w3a
    #
    @38
    @0
    @1
    @2
    @39
    w3a
    wa
    #
    @15
    c1
    @4
    @28
    @17
    @1
    @2
    @0
    simpr32
    c1
    cn0
    wcel
    #
    @40
    1nn0
    a1i
    nn0addcld
    3anassrs
    3anassrs
    @36
    cB
    c.x
    cM
    @18
    cX
    omndmul.0
    omndmul2.2
    mulgnn0cl
    syl3anc
    3jca
    @29
    @17
    simpr
    @29
    @34
    @17
    @29
    c.0
    @16
    cM
    cplusg
    cfv
    #
    co
    #
    cX
    @16
    @42
    co
    #
    @16
    @19
    c.le
    @29
    @0
    @23
    @1
    @31
    @4
    @43
    @44
    c.le
    wbr
    @0
    @1
    @2
    @4
    @28
    simp-4l
    @29
    @25
    @23
    @0
    @25
    @1
    @2
    @4
    @28
    @26
    ad4antr
    #
    @27
    syl
    @0
    @1
    @2
    @4
    @28
    simp-4r
    #
    @29
    @25
    @28
    @1
    @31
    @45
    @8
    @28
    simpr
    #
    @46
    @37
    syl3anc
    #
    @7
    @4
    @28
    simplr
    cB
    @42
    c.le
    cM
    c.0
    cX
    @16
    omndmul.0
    omndmul.1
    @42
    eqid
    #
    omndadd
    syl131anc
    @29
    @25
    @31
    @43
    @16
    wceq
    @45
    @48
    cB
    @42
    cM
    @16
    c.0
    omndmul.0
    @49
    omndmul2.3
    mndlid
    syl2anc
    @29
    c1
    @15
    caddc
    co
    #
    cX
    c.x
    co
    #
    c1
    cX
    c.x
    co
    #
    @16
    @42
    co
    #
    @19
    @44
    @29
    @25
    @41
    @28
    @1
    @51
    @53
    wceq
    @45
    @41
    @29
    1nn0
    a1i
    @47
    @46
    cB
    @42
    c.x
    cM
    c1
    @15
    cX
    omndmul.0
    omndmul2.2
    @49
    mulgnn0dir
    syl13anc
    @29
    @50
    @18
    cX
    c.x
    @6
    @2
    @4
    @28
    @50
    @18
    wceq
    @6
    @2
    @4
    @28
    w3a
    wa
    #
    c1
    @15
    @54
    1cnd
    @54
    @15
    @6
    @2
    @4
    @28
    simpr3
    nn0cnd
    addcomd
    3anassrs
    oveq1d
    @29
    @52
    cX
    @16
    @42
    @29
    @1
    @52
    cX
    wceq
    @46
    cB
    c.x
    cM
    cX
    omndmul.0
    omndmul2.2
    mulg1
    syl
    oveq1d
    3eqtr3rd
    3brtr3d
    adantr
    @22
    @33
    wa
    @17
    @34
    wa
    @20
    cB
    cM
    c.le
    c.0
    @16
    @19
    omndmul.0
    omndmul.1
    postr
    imp
    syl22anc
    nn0indd
    mpdan
    sylbi
end
