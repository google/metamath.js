include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cvsca.mm"
include "co.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "clmod.mm"
include "wb.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "lspsnel.mm"
include "syl2anc.mm"
include "wi.mm"
include "wne.mm"
include "wn.mm"
include "lshpnel.mm"
include "ad2antrr.mm"
include "clss.mm"
include "lshplss.mm"
include "simpr.mm"
include "lspsneli.mm"
include "lspsnel4.mm"
include "mtbid.mm"
include "ex.mm"
include "necon4ad.mm"
include "eleq1.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "com23.mm"
include "com24.mm"
include "imp31.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "expimpd.mm"
include "elin.mm"
include "velsn.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "wss.mm"
include "lspsncl.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "lss0ss.mm"
include "eqssd.mm"

theorem lshpdisj
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vv: setvar v
  assume lshpdisj.v: |- V = ( Base ` W )
  assume lshpdisj.o: |- .0. = ( 0g ` W )
  assume lshpdisj.n: |- N = ( LSpan ` W )
  assume lshpdisj.p: |- .(+) = ( LSSum ` W )
  assume lshpdisj.h: |- H = ( LSHyp ` W )
  assume lshpdisj.w: |- ( ph -> W e. LVec )
  assume lshpdisj.u: |- ( ph -> U e. H )
  assume lshpdisj.x: |- ( ph -> X e. V )
  assume lshpdisj.e: |- ( ph -> ( U .(+) ( N ` { X } ) ) = V )


  assert |- ( ph -> ( U i^i ( N ` { X } ) ) = { .0. } )

  proof
    wph
    cU
    cX
    csn
    cN
    cfv
    #
    cin
    #
    c.0
    csn
    #
    wph
    vv
    @1
    @2
    wph
    vv
    cv
    #
    cU
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    @3
    c.0
    wceq
    #
    @3
    @1
    wcel
    @3
    @2
    wcel
    wph
    @4
    @5
    @6
    wph
    @4
    wa
    #
    @5
    @3
    vk
    cv
    #
    cX
    cW
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    @6
    @7
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @5
    @14
    wb
    wph
    @15
    @4
    wph
    cW
    clvec
    wcel
    #
    @15
    lshpdisj.w
    cW
    lveclmod
    syl
    #
    adantr
    wph
    @16
    @4
    lshpdisj.x
    adantr
    @9
    @3
    vk
    @12
    @13
    cN
    cV
    cW
    cX
    @12
    eqid
    #
    @13
    eqid
    #
    lshpdisj.v
    @9
    eqid
    #
    lshpdisj.n
    lspsnel
    syl2anc
    @7
    @11
    @6
    vk
    @13
    wph
    @4
    @8
    @13
    wcel
    #
    @11
    @6
    wi
    wph
    @11
    @22
    @4
    @6
    wph
    @22
    @11
    @4
    @6
    wi
    #
    wph
    @22
    @11
    @23
    wi
    wph
    @22
    wa
    #
    @23
    @11
    @10
    cU
    wcel
    #
    @10
    c.0
    wceq
    #
    wi
    @24
    @25
    @10
    c.0
    @24
    @10
    c.0
    wne
    #
    @25
    wn
    @24
    @27
    wa
    #
    cX
    cU
    wcel
    #
    @25
    wph
    @29
    wn
    @22
    @27
    wph
    c.po
    cU
    cH
    cN
    cV
    cW
    cX
    lshpdisj.v
    lshpdisj.n
    lshpdisj.p
    lshpdisj.h
    @18
    lshpdisj.u
    lshpdisj.x
    lshpdisj.e
    lshpnel
    ad2antrr
    @28
    cW
    clss
    cfv
    #
    cU
    cN
    cV
    cW
    cX
    @10
    c.0
    lshpdisj.v
    lshpdisj.o
    @30
    eqid
    #
    lshpdisj.n
    wph
    @17
    @22
    @27
    lshpdisj.w
    ad2antrr
    wph
    cU
    @30
    wcel
    #
    @22
    @27
    wph
    @30
    cU
    cH
    cW
    @31
    lshpdisj.h
    @18
    lshpdisj.u
    lshplss
    #
    ad2antrr
    wph
    @16
    @22
    @27
    lshpdisj.x
    ad2antrr
    @24
    @10
    @0
    wcel
    @27
    @24
    @8
    @9
    @12
    @13
    cN
    cV
    cW
    cX
    lshpdisj.v
    @21
    @19
    @20
    lshpdisj.n
    wph
    @15
    @22
    @18
    adantr
    wph
    @22
    simpr
    wph
    @16
    @22
    lshpdisj.x
    adantr
    lspsneli
    adantr
    @24
    @27
    simpr
    lspsnel4
    mtbid
    ex
    necon4ad
    @11
    @4
    @25
    @6
    @26
    @3
    @10
    cU
    eleq1
    @3
    @10
    c.0
    eqeq1
    imbi12d
    syl5ibrcom
    ex
    com23
    com24
    imp31
    rexlimdva
    sylbid
    expimpd
    @3
    cU
    @0
    elin
    vv
    c.0
    velsn
    3imtr4g
    ssrdv
    wph
    @15
    @1
    @30
    wcel
    #
    @2
    @1
    wss
    @18
    wph
    @15
    @32
    @0
    @30
    wcel
    #
    @34
    @18
    @33
    wph
    @15
    @16
    @35
    @18
    lshpdisj.x
    @30
    cN
    cV
    cW
    cX
    lshpdisj.v
    @31
    lshpdisj.n
    lspsncl
    syl2anc
    @30
    cU
    @0
    cW
    @31
    lssincl
    syl3anc
    @30
    cW
    @1
    c.0
    lshpdisj.o
    @31
    lss0ss
    syl2anc
    eqssd
end
