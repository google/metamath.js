include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "eqid.mm"
include "clvec.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "clss.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lssneln0.mm"
include "wne.mm"
include "lspsnne2.mm"
include "simpr.mm"
include "lspexch.mm"
include "mtand.mm"

theorem lspexchn1
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lspexchn1.v: |- V = ( Base ` W )
  assume lspexchn1.n: |- N = ( LSpan ` W )
  assume lspexchn1.w: |- ( ph -> W e. LVec )
  assume lspexchn1.x: |- ( ph -> X e. V )
  assume lspexchn1.y: |- ( ph -> Y e. V )
  assume lspexchn1.z: |- ( ph -> Z e. V )
  assume lspexchn1.q: |- ( ph -> -. Y e. ( N ` { Z } ) )
  assume lspexchn1.e: |- ( ph -> -. X e. ( N ` { Y , Z } ) )


  assert |- ( ph -> -. Y e. ( N ` { X , Z } ) )

  proof
    wph
    cY
    cX
    cZ
    cpr
    cN
    cfv
    wcel
    #
    cX
    cY
    cZ
    cpr
    cN
    cfv
    wcel
    lspexchn1.e
    wph
    @0
    wa
    cN
    cV
    cW
    cY
    cX
    cW
    c0g
    cfv
    #
    cZ
    lspexchn1.v
    @1
    eqid
    #
    lspexchn1.n
    wph
    cW
    clvec
    wcel
    #
    @0
    lspexchn1.w
    adantr
    wph
    cY
    cV
    @1
    csn
    cdif
    wcel
    @0
    wph
    cW
    clss
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    cV
    cW
    cY
    @1
    lspexchn1.v
    @2
    @4
    eqid
    #
    wph
    @3
    cW
    clmod
    wcel
    #
    lspexchn1.w
    cW
    lveclmod
    syl
    #
    wph
    @7
    cZ
    cV
    wcel
    #
    @5
    @4
    wcel
    @8
    lspexchn1.z
    @4
    cN
    cV
    cW
    cZ
    lspexchn1.v
    @6
    lspexchn1.n
    lspsncl
    syl2anc
    lspexchn1.y
    lspexchn1.q
    lssneln0
    adantr
    wph
    cX
    cV
    wcel
    @0
    lspexchn1.x
    adantr
    wph
    @9
    @0
    lspexchn1.z
    adantr
    wph
    cY
    csn
    cN
    cfv
    @5
    wne
    @0
    wph
    cN
    cV
    cW
    cY
    cZ
    lspexchn1.v
    lspexchn1.n
    @8
    lspexchn1.y
    lspexchn1.z
    lspexchn1.q
    lspsnne2
    adantr
    wph
    @0
    simpr
    lspexch
    mtand
end
