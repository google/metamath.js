include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "crn.mm"
include "dvh2dim.mm"
include "w3a.mm"
include "cplusg.mm"
include "c0g.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "wceq.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "hdmaprnlem11N.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmaprnlem15N
  let wph: wff ph
  let vv: setvar v
  let cC: class C
  let cD: class D
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
  let vt: setvar t
  assume hdmaprnlem15.h: |- H = ( LHyp ` K )
  assume hdmaprnlem15.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaprnlem15.v: |- V = ( Base ` U )
  assume hdmaprnlem15.n: |- N = ( LSpan ` U )
  assume hdmaprnlem15.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmaprnlem15.d: |- D = ( Base ` C )
  assume hdmaprnlem15.q: |- .0. = ( 0g ` C )
  assume hdmaprnlem15.l: |- L = ( LSpan ` C )
  assume hdmaprnlem15.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmaprnlem15.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaprnlem15.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaprnlem15.se: |- ( ph -> s e. ( D \ { .0. } ) )
  assume hdmaprnlem15.ve: |- ( ph -> v e. V )
  assume hdmaprnlem15.e: |- ( ph -> ( M ` ( N ` { v } ) ) = ( L ` { s } ) )

  disjoint s v
  disjoint N t
  disjoint S t
  disjoint U t
  disjoint V t
  disjoint ph t
  disjoint s t
  disjoint t v
  assert |- ( ph -> s e. ran S )

  proof
    wph
    vt
    cv
    #
    vv
    cv
    #
    csn
    cN
    cfv
    #
    wcel
    wn
    #
    vt
    cV
    wrex
    vs
    cv
    #
    cS
    crn
    wcel
    #
    wph
    vt
    cU
    cH
    cK
    cN
    cV
    cW
    @1
    hdmaprnlem15.h
    hdmaprnlem15.u
    hdmaprnlem15.v
    hdmaprnlem15.n
    hdmaprnlem15.k
    hdmaprnlem15.ve
    dvh2dim
    wph
    @3
    @5
    vt
    cV
    wph
    @0
    cV
    wcel
    #
    @3
    w3a
    vv
    vt
    cC
    cD
    cU
    cplusg
    cfv
    #
    cC
    cplusg
    cfv
    #
    c.0
    cS
    cU
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    cU
    c0g
    cfv
    #
    vs
    hdmaprnlem15.h
    hdmaprnlem15.u
    hdmaprnlem15.v
    hdmaprnlem15.n
    hdmaprnlem15.c
    hdmaprnlem15.l
    hdmaprnlem15.m
    hdmaprnlem15.s
    wph
    @6
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    hdmaprnlem15.k
    3ad2ant1
    wph
    @6
    @4
    cD
    c.0
    csn
    cdif
    wcel
    @3
    hdmaprnlem15.se
    3ad2ant1
    wph
    @6
    @1
    cV
    wcel
    @3
    hdmaprnlem15.ve
    3ad2ant1
    wph
    @6
    @2
    cM
    cfv
    @4
    csn
    cL
    cfv
    wceq
    @3
    hdmaprnlem15.e
    3ad2ant1
    wph
    @6
    @3
    simp2
    wph
    @6
    @3
    simp3
    hdmaprnlem15.d
    hdmaprnlem15.q
    @9
    eqid
    @8
    eqid
    @7
    eqid
    hdmaprnlem11N
    rexlimdv3a
    mpd
end
