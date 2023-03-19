include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "hdmaprnlem3eN.mm"
include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "wn.mm"
include "simprl.mm"
include "hdmaprnlem4tN.mm"
include "simprr.mm"
include "hdmaprnlem9N.mm"
include "eqcomd.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"

theorem hdmaprnlem10N
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
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
  disjoint s u
  disjoint s v
  disjoint u v
  assert |- ( ph -> E. t e. V ( S ` t ) = s )

  proof
    wph
    vu
    cv
    #
    cS
    cfv
    vs
    cv
    #
    c.pb
    co
    csn
    cL
    cfv
    @0
    vt
    cv
    #
    c.pl
    co
    csn
    cN
    cfv
    cM
    cfv
    wceq
    #
    vt
    vv
    cv
    #
    csn
    cN
    cfv
    #
    c.0
    csn
    cdif
    #
    wrex
    @2
    cS
    cfv
    #
    @1
    wceq
    #
    vt
    cV
    wrex
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
    hdmaprnlem3eN
    wph
    @3
    @8
    vt
    @6
    cV
    wph
    @2
    @6
    wcel
    #
    @3
    wa
    #
    @2
    cV
    wcel
    #
    @8
    wa
    wph
    @10
    wa
    #
    @11
    @8
    @12
    vv
    vu
    vt
    cC
    cD
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
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @10
    hdmaprnlem1.k
    adantr
    #
    wph
    @1
    cD
    cQ
    csn
    cdif
    wcel
    @10
    hdmaprnlem1.se
    adantr
    #
    wph
    @4
    cV
    wcel
    @10
    hdmaprnlem1.ve
    adantr
    #
    wph
    @5
    cM
    cfv
    @1
    csn
    cL
    cfv
    wceq
    @10
    hdmaprnlem1.e
    adantr
    #
    wph
    @0
    cV
    wcel
    @10
    hdmaprnlem1.ue
    adantr
    #
    wph
    @0
    @5
    wcel
    wn
    @10
    hdmaprnlem1.un
    adantr
    #
    hdmaprnlem1.d
    hdmaprnlem1.q
    hdmaprnlem1.o
    hdmaprnlem1.a
    wph
    @9
    @3
    simprl
    #
    hdmaprnlem4tN
    @12
    @1
    @7
    @12
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
    @13
    @14
    @15
    @16
    @17
    @18
    hdmaprnlem1.d
    hdmaprnlem1.q
    hdmaprnlem1.o
    hdmaprnlem1.a
    @19
    hdmaprnlem3e.p
    wph
    @9
    @3
    simprr
    hdmaprnlem9N
    eqcomd
    jca
    ex
    reximdv2
    mpd
end
