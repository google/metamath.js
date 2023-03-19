include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "clss.mm"
include "wne.mm"
include "w3a.mm"
include "eqid.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "islshpsm.mm"
include "mpbid.mm"
include "simp3d.mm"
include "adantr.mm"
include "wpss.mm"
include "wss.mm"
include "simp1l.mm"
include "simp2.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "lshplss.mm"
include "sseldd.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmub1.mm"
include "lsmub2.mm"
include "lspsnid.mm"
include "nelne1.mm"
include "sylan.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "3ad2ant1.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lssss.mm"
include "simpr.mm"
include "sseqtr4d.mm"
include "adantlr.mm"
include "3adant2.mm"
include "lsmcv.mm"
include "syl211anc.mm"
include "simp3.mm"
include "eqtrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "lshpnel.mm"
include "impbida.mm"

theorem lshpnelb
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vv: setvar v
  assume lshpnelb.v: |- V = ( Base ` W )
  assume lshpnelb.n: |- N = ( LSpan ` W )
  assume lshpnelb.p: |- .(+) = ( LSSum ` W )
  assume lshpnelb.h: |- H = ( LSHyp ` W )
  assume lshpnelb.w: |- ( ph -> W e. LVec )
  assume lshpnelb.u: |- ( ph -> U e. H )
  assume lshpnelb.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( -. X e. U <-> ( U .(+) ( N ` { X } ) ) = V ) )

  proof
    wph
    cX
    cU
    wcel
    wn
    #
    cU
    cX
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cV
    wceq
    #
    wph
    @0
    wa
    #
    cU
    vv
    cv
    #
    csn
    cN
    cfv
    c.po
    co
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    @3
    wph
    @8
    @0
    wph
    cU
    cW
    clss
    cfv
    #
    wcel
    #
    cU
    cV
    wne
    #
    @8
    wph
    cU
    cH
    wcel
    #
    @10
    @11
    @8
    w3a
    lshpnelb.u
    wph
    vv
    c.po
    @9
    cU
    cH
    cN
    cV
    cW
    lshpnelb.v
    lshpnelb.n
    @9
    eqid
    #
    lshpnelb.p
    lshpnelb.h
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    lshpnelb.w
    cW
    lveclmod
    syl
    #
    islshpsm
    mpbid
    simp3d
    adantr
    @4
    @7
    @3
    vv
    cV
    @4
    @5
    cV
    wcel
    #
    @7
    w3a
    #
    @2
    @6
    cV
    @18
    wph
    @17
    cU
    @2
    wpss
    #
    @2
    @6
    wss
    #
    @2
    @6
    wceq
    wph
    @0
    @17
    @7
    simp1l
    @4
    @17
    @7
    simp2
    @4
    @17
    @19
    @7
    @4
    cU
    @2
    wss
    #
    cU
    @2
    wne
    @19
    wph
    @21
    @0
    wph
    cU
    cW
    csubg
    cfv
    #
    wcel
    #
    @1
    @22
    wcel
    #
    @21
    wph
    @9
    @22
    cU
    wph
    @15
    @9
    @22
    wss
    @16
    @9
    cW
    @13
    lsssssubg
    syl
    #
    wph
    @9
    cU
    cH
    cW
    @13
    lshpnelb.h
    @16
    lshpnelb.u
    lshplss
    #
    sseldd
    #
    wph
    @9
    @22
    @1
    @25
    wph
    @15
    cX
    cV
    wcel
    #
    @1
    @9
    wcel
    #
    @16
    lshpnelb.x
    @9
    cN
    cV
    cW
    cX
    lshpnelb.v
    @13
    lshpnelb.n
    lspsncl
    syl2anc
    #
    sseldd
    #
    c.po
    cU
    @1
    cW
    lshpnelb.p
    lsmub1
    syl2anc
    adantr
    @4
    @2
    cU
    wph
    cX
    @2
    wcel
    @0
    @2
    cU
    wne
    wph
    @1
    @2
    cX
    wph
    @23
    @24
    @1
    @2
    wss
    @27
    @31
    c.po
    cU
    @1
    cW
    lshpnelb.p
    lsmub2
    syl2anc
    wph
    @15
    @28
    cX
    @1
    wcel
    @16
    lshpnelb.x
    cN
    cV
    cW
    cX
    lshpnelb.v
    lshpnelb.n
    lspsnid
    syl2anc
    sseldd
    cX
    @2
    cU
    nelne1
    sylan
    necomd
    cU
    @2
    df-pss
    sylanbrc
    3ad2ant1
    @4
    @7
    @20
    @17
    wph
    @7
    @20
    @0
    wph
    @7
    wa
    @2
    cV
    @6
    wph
    @2
    cV
    wss
    #
    @7
    wph
    @2
    @9
    wcel
    #
    @32
    wph
    @15
    @10
    @29
    @33
    @16
    @26
    @30
    c.po
    @9
    cU
    @1
    cW
    @13
    lshpnelb.p
    lsmcl
    syl3anc
    #
    @9
    @2
    cV
    cW
    lshpnelb.v
    @13
    lssss
    syl
    adantr
    wph
    @7
    simpr
    sseqtr4d
    adantlr
    3adant2
    wph
    @17
    wa
    c.po
    @9
    cU
    @2
    cN
    cV
    cW
    @5
    lshpnelb.v
    @13
    lshpnelb.n
    lshpnelb.p
    wph
    @14
    @17
    lshpnelb.w
    adantr
    wph
    @10
    @17
    @26
    adantr
    wph
    @33
    @17
    @34
    adantr
    wph
    @17
    simpr
    lsmcv
    syl211anc
    @4
    @17
    @7
    simp3
    eqtrd
    rexlimdv3a
    mpd
    wph
    @3
    wa
    c.po
    cU
    cH
    cN
    cV
    cW
    cX
    lshpnelb.v
    lshpnelb.n
    lshpnelb.p
    lshpnelb.h
    wph
    @15
    @3
    @16
    adantr
    wph
    @12
    @3
    lshpnelb.u
    adantr
    wph
    @28
    @3
    lshpnelb.x
    adantr
    wph
    @3
    simpr
    lshpnel
    impbida
end
