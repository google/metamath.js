include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "ssel.mm"
include "syl5com.mm"
include "mtod.mm"
include "csn.mm"
include "clsm.mm"
include "co.mm"
include "wa.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "prssi.mm"
include "syl2anc.mm"
include "snsspr1.mm"
include "a1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "biantrurd.mm"
include "csubg.mm"
include "wb.mm"
include "clss.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "lspsncl.mm"
include "sseldd.mm"
include "lspprcl.mm"
include "lsmlub.mm"
include "bitrd.mm"
include "lspsnel5.mm"
include "lsmpr.mm"
include "sseq1d.mm"
include "3bitr4d.mm"
include "mtbird.mm"

theorem lspindp5
  let wph: wff ph
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lspindp5.v: |- V = ( Base ` W )
  assume lspindp5.n: |- N = ( LSpan ` W )
  assume lspindp5.w: |- ( ph -> W e. LVec )
  assume lspindp5.y: |- ( ph -> X e. V )
  assume lspindp5.x: |- ( ph -> Y e. V )
  assume lspindp5.u: |- ( ph -> U e. V )
  assume lspindp5.e: |- ( ph -> Z e. ( N ` { X , U } ) )
  assume lspindp5.m: |- ( ph -> -. Z e. ( N ` { X , Y } ) )


  assert |- ( ph -> -. U e. ( N ` { X , Y } ) )

  proof
    wph
    cU
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    cX
    cU
    cpr
    cN
    cfv
    #
    @1
    wss
    #
    wph
    @4
    cZ
    @1
    wcel
    #
    lspindp5.m
    wph
    cZ
    @3
    wcel
    @4
    @5
    lspindp5.e
    @3
    @1
    cZ
    ssel
    syl5com
    mtod
    wph
    cU
    csn
    cN
    cfv
    #
    @1
    wss
    #
    cX
    csn
    #
    cN
    cfv
    #
    @6
    cW
    clsm
    cfv
    #
    co
    #
    @1
    wss
    #
    @2
    @4
    wph
    @7
    @9
    @1
    wss
    #
    @7
    wa
    #
    @12
    wph
    @13
    @7
    wph
    cW
    clmod
    wcel
    #
    @0
    cV
    wss
    #
    @8
    @0
    wss
    #
    @13
    wph
    cW
    clvec
    wcel
    @15
    lspindp5.w
    cW
    lveclmod
    syl
    #
    wph
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    @16
    lspindp5.y
    lspindp5.x
    cX
    cY
    cV
    prssi
    syl2anc
    @17
    wph
    cX
    cY
    snsspr1
    a1i
    @8
    @0
    cN
    cV
    cW
    lspindp5.v
    lspindp5.n
    lspss
    syl3anc
    biantrurd
    wph
    @9
    cW
    csubg
    cfv
    #
    wcel
    @6
    @20
    wcel
    @1
    @20
    wcel
    @14
    @12
    wb
    wph
    cW
    clss
    cfv
    #
    @20
    @9
    wph
    @15
    @21
    @20
    wss
    @18
    @21
    cW
    @21
    eqid
    #
    lsssssubg
    syl
    #
    wph
    @15
    @19
    @9
    @21
    wcel
    @18
    lspindp5.y
    @21
    cN
    cV
    cW
    cX
    lspindp5.v
    @22
    lspindp5.n
    lspsncl
    syl2anc
    sseldd
    wph
    @21
    @20
    @6
    @23
    wph
    @15
    cU
    cV
    wcel
    @6
    @21
    wcel
    @18
    lspindp5.u
    @21
    cN
    cV
    cW
    cU
    lspindp5.v
    @22
    lspindp5.n
    lspsncl
    syl2anc
    sseldd
    wph
    @21
    @20
    @1
    @23
    wph
    @21
    cN
    cV
    cW
    cX
    cY
    lspindp5.v
    @22
    lspindp5.n
    @18
    lspindp5.y
    lspindp5.x
    lspprcl
    #
    sseldd
    @10
    @9
    @6
    @1
    cW
    @10
    eqid
    #
    lsmlub
    syl3anc
    bitrd
    wph
    @21
    @1
    cN
    cV
    cW
    cU
    lspindp5.v
    @22
    lspindp5.n
    @18
    @24
    lspindp5.u
    lspsnel5
    wph
    @3
    @11
    @1
    wph
    @10
    cN
    cV
    cW
    cX
    cU
    lspindp5.v
    lspindp5.n
    @25
    @18
    lspindp5.y
    lspindp5.u
    lsmpr
    sseq1d
    3bitr4d
    mtbird
end
