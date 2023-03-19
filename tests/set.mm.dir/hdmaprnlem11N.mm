include "cv.mm"
include "crn.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "hdmaprnlem10N.mm"
include "wfn.mm"
include "wb.mm"
include "hdmapfnN.mm"
include "fvelrnb.mm"
include "syl.mm"
include "mpbird.mm"

theorem hdmaprnlem11N
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cD: class D
  let c.pl: class .+
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
  let vt: setvar t
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
  assume hdmaprnlem3e.p: |- .+ = ( +g ` U )

  disjoint s u
  disjoint s v
  disjoint u v
  disjoint .+b t
  disjoint L t
  disjoint M t
  disjoint N t
  disjoint .0. t
  disjoint .+ t
  disjoint S t
  disjoint U t
  disjoint V t
  disjoint ph t
  disjoint s t
  disjoint t u
  disjoint t v
  assert |- ( ph -> s e. ran S )

  proof
    wph
    vs
    cv
    #
    cS
    crn
    wcel
    #
    vt
    cv
    cS
    cfv
    @0
    wceq
    vt
    cV
    wrex
    #
    wph
    vv
    vu
    vt
    cC
    cD
    c.pl
    c.pb
    cQ
    cS
    cU
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    c.0
    vs
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.v
    hdmaprnlem1.n
    hdmaprnlem1.c
    hdmaprnlem1.l
    hdmaprnlem1.m
    hdmaprnlem1.s
    hdmaprnlem1.k
    hdmaprnlem1.se
    hdmaprnlem1.ve
    hdmaprnlem1.e
    hdmaprnlem1.ue
    hdmaprnlem1.un
    hdmaprnlem1.d
    hdmaprnlem1.q
    hdmaprnlem1.o
    hdmaprnlem1.a
    hdmaprnlem3e.p
    hdmaprnlem10N
    wph
    cS
    cV
    wfn
    @1
    @2
    wb
    wph
    cS
    cU
    cH
    cK
    cV
    cW
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.v
    hdmaprnlem1.s
    hdmaprnlem1.k
    hdmapfnN
    vt
    cV
    @0
    cS
    fvelrnb
    syl
    mpbird
end
