include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "adantr.mm"
include "clvec.mm"
include "simpr.mm"
include "lshpnelb.mm"
include "mpbid.mm"
include "wne.mm"
include "cv.mm"
include "cun.mm"
include "wrex.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspid.mm"
include "syl2anc.mm"
include "uneq1d.mm"
include "fveq2d.mm"
include "wss.mm"
include "lssss.mm"
include "snssd.mm"
include "lspun.mm"
include "syl3anc.mm"
include "lspsncl.mm"
include "lsmsp.mm"
include "3eqtr4rd.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "sneq.mm"
include "uneq2d.mm"
include "rspcev.mm"
include "w3a.mm"
include "wb.mm"
include "islshp.mm"
include "mpbir3and.mm"
include "impbida.mm"

theorem lshpnel2N
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vv: setvar v
  assume lshpnel2.v: |- V = ( Base ` W )
  assume lshpnel2.s: |- S = ( LSubSp ` W )
  assume lshpnel2.n: |- N = ( LSpan ` W )
  assume lshpnel2.p: |- .(+) = ( LSSum ` W )
  assume lshpnel2.h: |- H = ( LSHyp ` W )
  assume lshpnel2.w: |- ( ph -> W e. LVec )
  assume lshpnel2.u: |- ( ph -> U e. S )
  assume lshpnel2.t: |- ( ph -> U =/= V )
  assume lshpnel2.x: |- ( ph -> X e. V )
  assume lshpnel2.e: |- ( ph -> -. X e. U )


  assert |- ( ph -> ( U e. H <-> ( U .(+) ( N ` { X } ) ) = V ) )

  proof
    wph
    cU
    cH
    wcel
    #
    cU
    cX
    csn
    #
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
    cX
    cU
    wcel
    wn
    #
    @4
    wph
    @6
    @0
    lshpnel2.e
    adantr
    @5
    c.po
    cU
    cH
    cN
    cV
    cW
    cX
    lshpnel2.v
    lshpnel2.n
    lshpnel2.p
    lshpnel2.h
    wph
    cW
    clvec
    wcel
    #
    @0
    lshpnel2.w
    adantr
    wph
    @0
    simpr
    wph
    cX
    cV
    wcel
    #
    @0
    lshpnel2.x
    adantr
    lshpnelb
    mpbid
    wph
    @4
    wa
    #
    @0
    cU
    cS
    wcel
    #
    cU
    cV
    wne
    #
    cU
    vv
    cv
    #
    csn
    #
    cun
    #
    cN
    cfv
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    wph
    @10
    @4
    lshpnel2.u
    adantr
    wph
    @11
    @4
    lshpnel2.t
    adantr
    @9
    @8
    cU
    @1
    cun
    #
    cN
    cfv
    #
    cV
    wceq
    #
    @17
    wph
    @8
    @4
    lshpnel2.x
    adantr
    wph
    @4
    @20
    wph
    @3
    @19
    cV
    wph
    cU
    cN
    cfv
    #
    @2
    cun
    #
    cN
    cfv
    #
    cU
    @2
    cun
    #
    cN
    cfv
    #
    @19
    @3
    wph
    @22
    @24
    cN
    wph
    @21
    cU
    @2
    wph
    cW
    clmod
    wcel
    #
    @10
    @21
    cU
    wceq
    wph
    @7
    @26
    lshpnel2.w
    cW
    lveclmod
    syl
    #
    lshpnel2.u
    cS
    cU
    cN
    cW
    lshpnel2.s
    lshpnel2.n
    lspid
    syl2anc
    uneq1d
    fveq2d
    wph
    @26
    cU
    cV
    wss
    #
    @1
    cV
    wss
    @19
    @23
    wceq
    @27
    wph
    @10
    @28
    lshpnel2.u
    cS
    cU
    cV
    cW
    lshpnel2.v
    lshpnel2.s
    lssss
    syl
    wph
    cX
    cV
    lshpnel2.x
    snssd
    cU
    @1
    cN
    cV
    cW
    lshpnel2.v
    lshpnel2.n
    lspun
    syl3anc
    wph
    @26
    @10
    @2
    cS
    wcel
    #
    @3
    @25
    wceq
    @27
    lshpnel2.u
    wph
    @26
    @8
    @29
    @27
    lshpnel2.x
    cS
    cN
    cV
    cW
    cX
    lshpnel2.v
    lshpnel2.s
    lshpnel2.n
    lspsncl
    syl2anc
    c.po
    cS
    cU
    @2
    cN
    cW
    lshpnel2.s
    lshpnel2.n
    lshpnel2.p
    lsmsp
    syl3anc
    3eqtr4rd
    eqeq1d
    biimpa
    @16
    @20
    vv
    cX
    cV
    @12
    cX
    wceq
    #
    @15
    @19
    cV
    @30
    @14
    @18
    cN
    @30
    @13
    @1
    cU
    @12
    cX
    sneq
    uneq2d
    fveq2d
    eqeq1d
    rspcev
    syl2anc
    @9
    @7
    @0
    @10
    @11
    @17
    w3a
    wb
    wph
    @7
    @4
    lshpnel2.w
    adantr
    vv
    cS
    cU
    cH
    cN
    cV
    cW
    clvec
    lshpnel2.v
    lshpnel2.n
    lshpnel2.s
    lshpnel2.h
    islshp
    syl
    mpbir3and
    impbida
end
