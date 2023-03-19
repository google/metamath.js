include "cn0.mm"
include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq12d.mm"
include "cpo.mm"
include "comnd.mm"
include "ctos.mm"
include "omndtos.mm"
include "tospos.mm"
include "3syl.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "mulg0.mm"
include "syl.mm"
include "cmnd.mm"
include "omndmnd.mm"
include "mndidcl.mm"
include "eqeltrd.mm"
include "posref.mm"
include "syl2anc.mm"
include "wb.mm"
include "wa.mm"
include "adantr.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "breq1d.mm"
include "mpbird.mm"
include "cplusg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "ccmn.mm"
include "omndadd2d.mm"
include "mulgnn0p1.mm"
include "3brtr4d.mm"
include "nn0indd.mm"
include "mpdan.mm"

theorem omndmul
  let wph: wff ph
  let cB: class B
  let c.x: class .x.
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let c.0: class .0.
  assume omndmul.0: |- B = ( Base ` M )
  assume omndmul.1: |- .<_ = ( le ` M )
  assume omndmul.2: |- .x. = ( .g ` M )
  assume omndmul.o: |- ( ph -> M e. oMnd )
  assume omndmul.c: |- ( ph -> M e. CMnd )
  assume omndmul.x: |- ( ph -> X e. B )
  assume omndmul.y: |- ( ph -> Y e. B )
  assume omndmul.n: |- ( ph -> N e. NN0 )
  assume omndmul.l: |- ( ph -> X .<_ Y )


  assert |- ( ph -> ( N .x. X ) .<_ ( N .x. Y ) )

  proof
    wph
    cN
    cn0
    wcel
    cN
    cX
    c.x
    co
    #
    cN
    cY
    c.x
    co
    #
    c.le
    wbr
    #
    omndmul.n
    wph
    vm
    cv
    #
    cX
    c.x
    co
    #
    @3
    cY
    c.x
    co
    #
    c.le
    wbr
    cc0
    cX
    c.x
    co
    #
    cc0
    cY
    c.x
    co
    #
    c.le
    wbr
    #
    vn
    cv
    #
    cX
    c.x
    co
    #
    @9
    cY
    c.x
    co
    #
    c.le
    wbr
    #
    @9
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    @13
    cY
    c.x
    co
    #
    c.le
    wbr
    @2
    vm
    vn
    cN
    @3
    cc0
    wceq
    @4
    @6
    @5
    @7
    c.le
    @3
    cc0
    cX
    c.x
    oveq1
    @3
    cc0
    cY
    c.x
    oveq1
    breq12d
    @3
    @9
    wceq
    @4
    @10
    @5
    @11
    c.le
    @3
    @9
    cX
    c.x
    oveq1
    @3
    @9
    cY
    c.x
    oveq1
    breq12d
    @3
    @13
    wceq
    @4
    @14
    @5
    @15
    c.le
    @3
    @13
    cX
    c.x
    oveq1
    @3
    @13
    cY
    c.x
    oveq1
    breq12d
    @3
    cN
    wceq
    @4
    @0
    @5
    @1
    c.le
    @3
    cN
    cX
    c.x
    oveq1
    @3
    cN
    cY
    c.x
    oveq1
    breq12d
    wph
    @8
    @7
    @7
    c.le
    wbr
    #
    wph
    cM
    cpo
    wcel
    #
    @7
    cB
    wcel
    @16
    wph
    cM
    comnd
    wcel
    #
    cM
    ctos
    wcel
    @17
    omndmul.o
    cM
    omndtos
    cM
    tospos
    3syl
    wph
    @7
    cM
    c0g
    cfv
    #
    cB
    wph
    cY
    cB
    wcel
    #
    @7
    @19
    wceq
    #
    omndmul.y
    cB
    c.x
    cM
    cY
    @19
    omndmul.0
    @19
    eqid
    #
    omndmul.2
    mulg0
    #
    syl
    wph
    @18
    cM
    cmnd
    wcel
    #
    @19
    cB
    wcel
    omndmul.o
    cM
    omndmnd
    #
    cB
    cM
    @19
    omndmul.0
    @22
    mndidcl
    3syl
    eqeltrd
    cB
    cM
    c.le
    @7
    omndmul.0
    omndmul.1
    posref
    syl2anc
    wph
    cX
    cB
    wcel
    #
    @20
    @8
    @16
    wb
    omndmul.x
    omndmul.y
    @26
    @20
    wa
    #
    @6
    @7
    @7
    c.le
    @27
    @6
    @19
    @7
    @26
    @6
    @19
    wceq
    @20
    cB
    c.x
    cM
    cX
    @19
    omndmul.0
    @22
    omndmul.2
    mulg0
    adantr
    @20
    @21
    @26
    @23
    adantl
    eqtr4d
    breq1d
    syl2anc
    mpbird
    wph
    @9
    cn0
    wcel
    #
    wa
    #
    @12
    wa
    #
    @10
    cX
    cM
    cplusg
    cfv
    #
    co
    #
    @11
    cY
    @31
    co
    #
    @14
    @15
    c.le
    @30
    cB
    @31
    c.le
    cM
    cY
    @10
    cX
    @11
    omndmul.0
    omndmul.1
    @31
    eqid
    #
    wph
    @18
    @28
    @12
    omndmul.o
    ad2antrr
    #
    wph
    @20
    @28
    @12
    omndmul.y
    ad2antrr
    #
    @30
    @24
    @28
    @26
    @10
    cB
    wcel
    @30
    @18
    @24
    @35
    @25
    syl
    #
    wph
    @28
    @12
    simplr
    #
    wph
    @26
    @28
    @12
    omndmul.x
    ad2antrr
    #
    cB
    c.x
    cM
    @9
    cX
    omndmul.0
    omndmul.2
    mulgnn0cl
    syl3anc
    @39
    @30
    @24
    @28
    @20
    @11
    cB
    wcel
    @37
    @38
    @36
    cB
    c.x
    cM
    @9
    cY
    omndmul.0
    omndmul.2
    mulgnn0cl
    syl3anc
    @29
    @12
    simpr
    wph
    cX
    cY
    c.le
    wbr
    @28
    @12
    omndmul.l
    ad2antrr
    wph
    cM
    ccmn
    wcel
    @28
    @12
    omndmul.c
    ad2antrr
    omndadd2d
    @30
    @24
    @28
    @26
    @14
    @32
    wceq
    @37
    @38
    @39
    cB
    @31
    c.x
    cM
    @9
    cX
    omndmul.0
    omndmul.2
    @34
    mulgnn0p1
    syl3anc
    @30
    @24
    @28
    @20
    @15
    @33
    wceq
    @37
    @38
    @36
    cB
    @31
    c.x
    cM
    @9
    cY
    omndmul.0
    omndmul.2
    @34
    mulgnn0p1
    syl3anc
    3brtr4d
    nn0indd
    mpdan
end
