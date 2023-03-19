include "wne.mm"
include "wcel.mm"
include "wn.mm"
include "lshpne.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "co.mm"
include "csubg.mm"
include "wss.mm"
include "clss.mm"
include "clmod.mm"
include "adantr.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "lshplss.mm"
include "sseldd.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "lspsnel5a.mm"
include "lsmss2.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem lshpnel
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lshpnel.v: |- V = ( Base ` W )
  assume lshpnel.n: |- N = ( LSpan ` W )
  assume lshpnel.p: |- .(+) = ( LSSum ` W )
  assume lshpnel.h: |- H = ( LSHyp ` W )
  assume lshpnel.w: |- ( ph -> W e. LMod )
  assume lshpnel.u: |- ( ph -> U e. H )
  assume lshpnel.x: |- ( ph -> X e. V )
  assume lshpnel.e: |- ( ph -> ( U .(+) ( N ` { X } ) ) = V )


  assert |- ( ph -> -. X e. U )

  proof
    wph
    cU
    cV
    wne
    cX
    cU
    wcel
    #
    wn
    wph
    cU
    cH
    cV
    cW
    lshpnel.v
    lshpnel.h
    lshpnel.w
    lshpnel.u
    lshpne
    wph
    @0
    cU
    cV
    wph
    @0
    cU
    cV
    wceq
    wph
    @0
    wa
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
    cU
    cV
    @1
    cU
    cW
    csubg
    cfv
    #
    wcel
    @2
    @4
    wcel
    @2
    cU
    wss
    @3
    cU
    wceq
    @1
    cW
    clss
    cfv
    #
    @4
    cU
    @1
    cW
    clmod
    wcel
    #
    @5
    @4
    wss
    wph
    @6
    @0
    lshpnel.w
    adantr
    #
    @5
    cW
    @5
    eqid
    #
    lsssssubg
    syl
    #
    wph
    cU
    @5
    wcel
    @0
    wph
    @5
    cU
    cH
    cW
    @8
    lshpnel.h
    lshpnel.w
    lshpnel.u
    lshplss
    adantr
    #
    sseldd
    @1
    @5
    @4
    @2
    @9
    @1
    @6
    cX
    cV
    wcel
    #
    @2
    @5
    wcel
    @7
    wph
    @11
    @0
    lshpnel.x
    adantr
    @5
    cN
    cV
    cW
    cX
    lshpnel.v
    @8
    lshpnel.n
    lspsncl
    syl2anc
    sseldd
    @1
    @5
    cU
    cN
    cW
    cX
    @8
    lshpnel.n
    @7
    @10
    wph
    @0
    simpr
    lspsnel5a
    c.po
    cU
    @2
    cW
    lshpnel.p
    lsmss2
    syl3anc
    wph
    @3
    cV
    wceq
    @0
    lshpnel.e
    adantr
    eqtr3d
    ex
    necon3ad
    mpd
end
