include "coml.mm"
include "wcel.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "coc.mm"
include "cmee.mm"
include "co.mm"
include "cp0.mm"
include "wceq.mm"
include "simpl2.mm"
include "wss.mm"
include "ssrab2.mm"
include "atssbase.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "lubss.mm"
include "mp3an23.mm"
include "syl.mm"
include "cpo.mm"
include "atlpos.mm"
include "3ad2ant3.mm"
include "simpl.mm"
include "simpr.mm"
include "lubid.mm"
include "sylan.mm"
include "breqtrd.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "breq1.mm"
include "elrab.mm"
include "simpll2.mm"
include "sstri.mm"
include "lubel.mm"
include "mp3an3.mm"
include "sylancom.mm"
include "ex.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "wne.mm"
include "simpll3.mm"
include "eqid.mm"
include "atn0.mm"
include "adantr.mm"
include "clat.mm"
include "wb.mm"
include "simpl3.mm"
include "atllat.mm"
include "atbase.mm"
include "adantl.mm"
include "clatlubcl.mm"
include "sylancl.mm"
include "cops.mm"
include "simpl1.mm"
include "omlop.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "opnoncon.mm"
include "breq2d.mm"
include "ople0.mm"
include "syl2an.mm"
include "3bitrd.mm"
include "biimpa.mm"
include "expr.mm"
include "necon3ad.mm"
include "mpd.mm"
include "syld.mm"
include "imnan.mm"
include "sylib.mm"
include "simplr.mm"
include "mtbid.mm"
include "nrexdv.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "atlex.mm"
include "necon1bd.mm"
include "omllaw3.mm"
include "mp2and.mm"

theorem atlatmstc
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.1: class .1.
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vx: setvar x
  assume atlatmstc.b: |- B = ( Base ` K )
  assume atlatmstc.l: |- .<_ = ( le ` K )
  assume atlatmstc.u: |- .1. = ( lub ` K )
  assume atlatmstc.a: |- A = ( Atoms ` K )

  disjoint .<_ y
  disjoint A y
  disjoint B y
  disjoint X y
  disjoint x y
  disjoint .<_ x
  disjoint .1. x
  disjoint A x
  disjoint B x
  disjoint X x
  disjoint K x
  assert |- ( ( ( K e. OML /\ K e. CLat /\ K e. AtLat ) /\ X e. B ) -> ( .1. ` { y e. A | y .<_ X } ) = X )

  proof
    cK
    coml
    wcel
    #
    cK
    ccla
    wcel
    #
    cK
    cal
    wcel
    #
    w3a
    #
    cX
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    cX
    c.le
    wbr
    #
    vy
    cA
    crab
    #
    c.1
    cfv
    #
    cX
    c.le
    wbr
    #
    cX
    @9
    cK
    coc
    cfv
    #
    cfv
    #
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cp0
    cfv
    #
    wceq
    #
    @9
    cX
    wceq
    #
    @5
    @9
    @7
    vy
    cB
    crab
    #
    c.1
    cfv
    #
    cX
    c.le
    @5
    @1
    @9
    @19
    c.le
    wbr
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    @1
    @18
    cB
    wss
    @8
    @18
    wss
    #
    @20
    @7
    vy
    cB
    ssrab2
    cA
    cB
    wss
    @22
    cA
    cB
    cK
    atlatmstc.b
    atlatmstc.a
    atssbase
    #
    @7
    vy
    cA
    cB
    rabss2
    ax-mp
    cB
    @8
    @18
    c.1
    cK
    c.le
    atlatmstc.b
    atlatmstc.l
    atlatmstc.u
    lubss
    mp3an23
    syl
    @3
    cK
    cpo
    wcel
    #
    @4
    @19
    cX
    wceq
    @2
    @0
    @24
    @1
    cK
    atlpos
    3ad2ant3
    @24
    @4
    wa
    vy
    cB
    c.1
    cK
    c.le
    cX
    atlatmstc.b
    atlatmstc.l
    atlatmstc.u
    @24
    @4
    simpl
    @24
    @4
    simpr
    lubid
    sylan
    breqtrd
    @5
    vx
    cv
    #
    @14
    c.le
    wbr
    #
    vx
    cA
    wrex
    #
    wn
    @16
    @5
    @26
    vx
    cA
    @5
    @25
    cA
    wcel
    #
    wa
    #
    @25
    cX
    c.le
    wbr
    #
    @25
    @12
    c.le
    wbr
    #
    wa
    #
    @26
    @29
    @30
    @31
    wn
    #
    wi
    @32
    wn
    @29
    @30
    @25
    @9
    c.le
    wbr
    #
    @33
    @5
    @28
    @30
    @34
    @28
    @30
    wa
    @25
    @8
    wcel
    #
    @5
    @34
    @7
    @30
    vy
    @25
    cA
    @6
    @25
    cX
    c.le
    breq1
    elrab
    @5
    @35
    @34
    @5
    @35
    @1
    @34
    @0
    @1
    @2
    @4
    @35
    simpll2
    @1
    @35
    @8
    cB
    wss
    #
    @34
    @8
    cA
    cB
    @7
    vy
    cA
    ssrab2
    @23
    sstri
    #
    cB
    @8
    c.1
    cK
    c.le
    @25
    atlatmstc.b
    atlatmstc.l
    atlatmstc.u
    lubel
    mp3an3
    sylancom
    ex
    syl5bir
    expdimp
    @29
    @34
    @33
    @29
    @34
    wa
    #
    @25
    @15
    wne
    #
    @33
    @29
    @39
    @34
    @5
    @28
    @2
    @39
    @0
    @1
    @2
    @4
    @28
    simpll3
    cA
    @25
    cK
    @15
    @15
    eqid
    #
    atlatmstc.a
    atn0
    sylancom
    adantr
    @38
    @31
    @25
    @15
    @29
    @34
    @31
    @25
    @15
    wceq
    #
    @29
    @34
    @31
    wa
    #
    @41
    @29
    @42
    @25
    @9
    @12
    @13
    co
    #
    c.le
    wbr
    #
    @25
    @15
    c.le
    wbr
    #
    @41
    @29
    cK
    clat
    wcel
    #
    @25
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @42
    @44
    wb
    @5
    @46
    @28
    @5
    @2
    @46
    @0
    @1
    @2
    @4
    simpl3
    cK
    atllat
    syl
    #
    adantr
    #
    @28
    @47
    @5
    cA
    cB
    @25
    cK
    atlatmstc.b
    atlatmstc.a
    atbase
    #
    adantl
    #
    @5
    @48
    @28
    @5
    @1
    @36
    @48
    @21
    @37
    cB
    @8
    c.1
    cK
    atlatmstc.b
    atlatmstc.u
    clatlubcl
    sylancl
    #
    adantr
    @5
    @49
    @28
    @5
    cK
    cops
    wcel
    #
    @48
    @49
    @5
    @0
    @55
    @0
    @1
    @2
    @4
    simpl1
    #
    cK
    omlop
    syl
    #
    @54
    cB
    cK
    @11
    @9
    atlatmstc.b
    @11
    eqid
    #
    opoccl
    syl2anc
    #
    adantr
    #
    cB
    cK
    c.le
    @13
    @25
    @9
    @12
    atlatmstc.b
    atlatmstc.l
    @13
    eqid
    #
    latlem12
    syl13anc
    @5
    @44
    @45
    wb
    @28
    @5
    @43
    @15
    @25
    c.le
    @5
    @55
    @48
    @43
    @15
    wceq
    @57
    @54
    cB
    cK
    @13
    @11
    @9
    @15
    atlatmstc.b
    @58
    @61
    @40
    opnoncon
    syl2anc
    breq2d
    adantr
    @5
    @55
    @47
    @45
    @41
    wb
    @28
    @57
    @52
    cB
    cK
    c.le
    @25
    @15
    atlatmstc.b
    atlatmstc.l
    @40
    ople0
    syl2an
    3bitrd
    biimpa
    expr
    necon3ad
    mpd
    ex
    syld
    @30
    @31
    imnan
    sylib
    @29
    @46
    @47
    @4
    @49
    @32
    @26
    wb
    @51
    @53
    @3
    @4
    @28
    simplr
    @60
    cB
    cK
    c.le
    @13
    @25
    cX
    @12
    atlatmstc.b
    atlatmstc.l
    @61
    latlem12
    syl13anc
    mtbid
    nrexdv
    @5
    @27
    @14
    @15
    @5
    @14
    @15
    wne
    #
    @27
    @5
    @62
    wa
    @2
    @14
    cB
    wcel
    #
    @62
    @27
    @0
    @1
    @2
    @4
    @62
    simpll3
    @5
    @63
    @62
    @5
    @46
    @4
    @49
    @63
    @50
    @3
    @4
    simpr
    #
    @59
    cB
    cK
    @13
    cX
    @12
    atlatmstc.b
    @61
    latmcl
    syl3anc
    adantr
    @5
    @62
    simpr
    vx
    cA
    cB
    cK
    c.le
    @14
    @15
    atlatmstc.b
    atlatmstc.l
    @40
    atlatmstc.a
    atlex
    syl3anc
    ex
    necon1bd
    mpd
    @5
    @0
    @48
    @4
    @10
    @16
    wa
    @17
    wi
    @56
    @54
    @64
    cB
    cK
    c.le
    @13
    @11
    @9
    cX
    @15
    atlatmstc.b
    atlatmstc.l
    @61
    @58
    @40
    omllaw3
    syl3anc
    mp2and
end
