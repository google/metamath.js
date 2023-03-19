include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "lshpnel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "clss.mm"
include "cfv.mm"
include "eqid.mm"
include "clmod.mm"
include "adantr.mm"
include "lshplss.mm"
include "simpr.mm"
include "lssneln0.mm"
include "eldifsni.mm"
include "syl.mm"
include "mpdan.mm"

theorem lshpne0
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lshpne0.v: |- V = ( Base ` W )
  assume lshpne0.n: |- N = ( LSpan ` W )
  assume lshpne0.p: |- .(+) = ( LSSum ` W )
  assume lshpne0.h: |- H = ( LSHyp ` W )
  assume lshpne0.o: |- .0. = ( 0g ` W )
  assume lshpne0.w: |- ( ph -> W e. LMod )
  assume lshpne0.u: |- ( ph -> U e. H )
  assume lshpne0.x: |- ( ph -> X e. V )
  assume lshpne0.e: |- ( ph -> ( U .(+) ( N ` { X } ) ) = V )


  assert |- ( ph -> X =/= .0. )

  proof
    wph
    cX
    cU
    wcel
    wn
    #
    cX
    c.0
    wne
    #
    wph
    c.po
    cU
    cH
    cN
    cV
    cW
    cX
    lshpne0.v
    lshpne0.n
    lshpne0.p
    lshpne0.h
    lshpne0.w
    lshpne0.u
    lshpne0.x
    lshpne0.e
    lshpnel
    wph
    @0
    wa
    #
    cX
    cV
    c.0
    csn
    cdif
    wcel
    @1
    @2
    cW
    clss
    cfv
    #
    cU
    cV
    cW
    cX
    c.0
    lshpne0.v
    lshpne0.o
    @3
    eqid
    #
    wph
    cW
    clmod
    wcel
    @0
    lshpne0.w
    adantr
    wph
    cU
    @3
    wcel
    @0
    wph
    @3
    cU
    cH
    cW
    @4
    lshpne0.h
    lshpne0.w
    lshpne0.u
    lshplss
    adantr
    wph
    cX
    cV
    wcel
    @0
    lshpne0.x
    adantr
    wph
    @0
    simpr
    lssneln0
    cX
    cV
    c.0
    eldifsni
    syl
    mpdan
end
