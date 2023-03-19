include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cdif.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "dvhlmod.mm"
include "snssd.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "ssdifssd.mm"
include "sseldd.mm"

theorem hdmaprnlem4tN
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cC: class C
  let cD: class D
  let c.pb: class .+b
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  assume hdmaprnlem1.h: |- H = ( LHyp ` K )
  assume hdmaprnlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaprnlem1.v: |- V = ( Base ` U )
  assume hdmaprnlem1.n: |- N = ( LSpan ` U )
  assume hdmaprnlem1.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmaprnlem1.l: |- L = ( LSpan ` C )
  assume hdmaprnlem1.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmaprnlem1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaprnlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaprnlem1.se: |- ( ph -> s e. ( D \ { Q } ) )
  assume hdmaprnlem1.ve: |- ( ph -> v e. V )
  assume hdmaprnlem1.e: |- ( ph -> ( M ` ( N ` { v } ) ) = ( L ` { s } ) )
  assume hdmaprnlem1.ue: |- ( ph -> u e. V )
  assume hdmaprnlem1.un: |- ( ph -> -. u e. ( N ` { v } ) )
  assume hdmaprnlem1.d: |- D = ( Base ` C )
  assume hdmaprnlem1.q: |- Q = ( 0g ` C )
  assume hdmaprnlem1.o: |- .0. = ( 0g ` U )
  assume hdmaprnlem1.a: |- .+b = ( +g ` C )
  assume hdmaprnlem1.t2: |- ( ph -> t e. ( ( N ` { v } ) \ { .0. } ) )


  assert |- ( ph -> t e. V )

  proof
    wph
    vv
    cv
    #
    csn
    #
    cN
    cfv
    #
    c.0
    csn
    #
    cdif
    cV
    vt
    cv
    wph
    @2
    cV
    @3
    wph
    cU
    clmod
    wcel
    @1
    cV
    wss
    @2
    cV
    wss
    wph
    cU
    cH
    cK
    cW
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.k
    dvhlmod
    wph
    @0
    cV
    hdmaprnlem1.ve
    snssd
    @1
    cN
    cV
    cU
    hdmaprnlem1.v
    hdmaprnlem1.n
    lspssv
    syl2anc
    ssdifssd
    hdmaprnlem1.t2
    sseldd
end
