include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "clss.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "clmod.mm"
include "wcel.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "lspsnel5a.mm"
include "dvhlvec.mm"
include "cdif.mm"
include "lss1.mm"
include "syl.mm"
include "ssdifd.mm"
include "sseldd.mm"
include "lspsncmp.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem hdmaprnlem4N
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


  assert |- ( ph -> ( M ` ( N ` { t } ) ) = ( L ` { s } ) )

  proof
    wph
    vt
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    vv
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    vs
    cv
    csn
    cL
    cfv
    wph
    @1
    @3
    cM
    wph
    @1
    @3
    wss
    @1
    @3
    wceq
    wph
    cU
    clss
    cfv
    #
    @3
    cN
    cU
    @0
    @4
    eqid
    #
    hdmaprnlem1.n
    wph
    cU
    cH
    cK
    cW
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.k
    dvhlmod
    #
    wph
    cU
    clmod
    wcel
    #
    @2
    cV
    wcel
    @3
    @4
    wcel
    @6
    hdmaprnlem1.ve
    @4
    cN
    cV
    cU
    @2
    hdmaprnlem1.v
    @5
    hdmaprnlem1.n
    lspsncl
    syl2anc
    wph
    @0
    @3
    c.0
    csn
    #
    hdmaprnlem1.t2
    eldifad
    lspsnel5a
    wph
    cN
    cV
    cU
    @0
    @2
    c.0
    hdmaprnlem1.v
    hdmaprnlem1.o
    hdmaprnlem1.n
    wph
    cU
    cH
    cK
    cW
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.k
    dvhlvec
    wph
    @3
    @8
    cdif
    cV
    @8
    cdif
    @0
    wph
    @3
    cV
    @8
    wph
    @4
    cV
    cN
    cU
    @2
    @5
    hdmaprnlem1.n
    @6
    wph
    @7
    cV
    @4
    wcel
    @6
    @4
    cV
    cU
    hdmaprnlem1.v
    @5
    lss1
    syl
    hdmaprnlem1.ve
    lspsnel5a
    ssdifd
    hdmaprnlem1.t2
    sseldd
    hdmaprnlem1.ve
    lspsncmp
    mpbid
    fveq2d
    hdmaprnlem1.e
    eqtrd
end
