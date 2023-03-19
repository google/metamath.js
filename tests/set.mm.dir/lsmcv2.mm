include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "csubg.mm"
include "clmod.mm"
include "wcel.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lssnle.mm"
include "mpbid.mm"
include "w3a.mm"
include "3simpa.mm"
include "simp3l.mm"
include "simp3r.mm"
include "adantr.mm"
include "simpr.mm"
include "lsmcv.mm"
include "syl3anc.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "lsmcl.mm"
include "lcvbr2.mm"
include "mpbir2and.mm"

theorem lsmcv2
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume lsmcv2.v: |- V = ( Base ` W )
  assume lsmcv2.s: |- S = ( LSubSp ` W )
  assume lsmcv2.n: |- N = ( LSpan ` W )
  assume lsmcv2.p: |- .(+) = ( LSSum ` W )
  assume lsmcv2.c: |- C = ( <oL ` W )
  assume lsmcv2.w: |- ( ph -> W e. LVec )
  assume lsmcv2.u: |- ( ph -> U e. S )
  assume lsmcv2.x: |- ( ph -> X e. V )
  assume lsmcv2.l: |- ( ph -> -. ( N ` { X } ) C_ U )


  assert |- ( ph -> U C ( U .(+) ( N ` { X } ) ) )

  proof
    wph
    cU
    cU
    cX
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cC
    wbr
    cU
    @1
    wpss
    #
    cU
    vx
    cv
    #
    wpss
    #
    @3
    @1
    wss
    #
    wa
    #
    @3
    @1
    wceq
    #
    wi
    #
    vx
    cS
    wral
    wph
    @0
    cU
    wss
    wn
    @2
    lsmcv2.l
    wph
    c.po
    cU
    @0
    cW
    lsmcv2.p
    wph
    cS
    cW
    csubg
    cfv
    #
    cU
    wph
    cW
    clmod
    wcel
    #
    cS
    @9
    wss
    wph
    cW
    clvec
    wcel
    #
    @10
    lsmcv2.w
    cW
    lveclmod
    syl
    #
    cS
    cW
    lsmcv2.s
    lsssssubg
    syl
    #
    lsmcv2.u
    sseldd
    wph
    cS
    @9
    @0
    @13
    wph
    @10
    cX
    cV
    wcel
    #
    @0
    cS
    wcel
    #
    @12
    lsmcv2.x
    cS
    cN
    cV
    cW
    cX
    lsmcv2.v
    lsmcv2.s
    lsmcv2.n
    lspsncl
    syl2anc
    #
    sseldd
    lssnle
    mpbid
    wph
    @8
    vx
    cS
    wph
    @3
    cS
    wcel
    #
    @6
    @7
    wph
    @17
    @6
    w3a
    wph
    @17
    wa
    #
    @4
    @5
    @7
    wph
    @17
    @6
    3simpa
    wph
    @17
    @4
    @5
    simp3l
    wph
    @17
    @4
    @5
    simp3r
    @18
    c.po
    cS
    cU
    @3
    cN
    cV
    cW
    cX
    lsmcv2.v
    lsmcv2.s
    lsmcv2.n
    lsmcv2.p
    wph
    @11
    @17
    lsmcv2.w
    adantr
    wph
    cU
    cS
    wcel
    #
    @17
    lsmcv2.u
    adantr
    wph
    @17
    simpr
    wph
    @14
    @17
    lsmcv2.x
    adantr
    lsmcv
    syl3anc
    3exp
    ralrimiv
    wph
    cC
    cS
    cU
    @1
    cW
    clvec
    vx
    lsmcv2.s
    lsmcv2.c
    lsmcv2.w
    lsmcv2.u
    wph
    @10
    @19
    @15
    @1
    cS
    wcel
    @12
    lsmcv2.u
    @16
    c.po
    cS
    cU
    @0
    cW
    lsmcv2.s
    lsmcv2.p
    lsmcl
    syl3anc
    lcvbr2
    mpbir2and
end
