include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "dvhlmod.mm"
include "lspsnne2.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapd11.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "hdmap10.mm"
include "3netr3d.mm"

theorem hdmaprnlem1N
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cD: class D
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


  assert |- ( ph -> ( L ` { ( S ` u ) } ) =/= ( L ` { s } ) )

  proof
    wph
    vu
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    vv
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    @0
    cS
    cfv
    csn
    cL
    cfv
    vs
    cv
    csn
    cL
    cfv
    wph
    @2
    @5
    wne
    @1
    @4
    wne
    wph
    cN
    cV
    cU
    @0
    @3
    hdmaprnlem1.v
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
    hdmaprnlem1.ue
    hdmaprnlem1.ve
    hdmaprnlem1.un
    lspsnne2
    wph
    @2
    @5
    @1
    @4
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    cM
    cW
    @1
    @4
    hdmaprnlem1.h
    hdmaprnlem1.u
    @7
    eqid
    #
    hdmaprnlem1.m
    hdmaprnlem1.k
    wph
    cU
    clmod
    wcel
    #
    @0
    cV
    wcel
    @1
    @7
    wcel
    @6
    hdmaprnlem1.ue
    @7
    cN
    cV
    cU
    @0
    hdmaprnlem1.v
    @8
    hdmaprnlem1.n
    lspsncl
    syl2anc
    wph
    @9
    @3
    cV
    wcel
    @4
    @7
    wcel
    @6
    hdmaprnlem1.ve
    @7
    cN
    cV
    cU
    @3
    hdmaprnlem1.v
    @8
    hdmaprnlem1.n
    lspsncl
    syl2anc
    mapd11
    necon3bid
    mpbird
    wph
    cC
    cS
    @0
    cU
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.v
    hdmaprnlem1.n
    hdmaprnlem1.c
    hdmaprnlem1.l
    hdmaprnlem1.m
    hdmaprnlem1.s
    hdmaprnlem1.k
    hdmaprnlem1.ue
    hdmap10
    hdmaprnlem1.e
    3netr3d
end
