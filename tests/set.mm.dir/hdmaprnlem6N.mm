include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "hdmaprnlem4tN.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "hdmap10.mm"
include "hdmapadd.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "3eqtrd.mm"

theorem hdmaprnlem6N
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
  assume hdmaprnlem1.t2: |- ( ph -> t e. ( ( N ` { v } ) \ { .0. } ) )
  assume hdmaprnlem1.p: |- .+ = ( +g ` U )
  assume hdmaprnlem1.pt: |- ( ph -> ( L ` { ( ( S ` u ) .+b s ) } ) = ( M ` ( N ` { ( u .+ t ) } ) ) )


  assert |- ( ph -> ( L ` { ( ( S ` u ) .+b s ) } ) = ( L ` { ( ( S ` u ) .+b ( S ` t ) ) } ) )

  proof
    wph
    vu
    cv
    #
    cS
    cfv
    #
    vs
    cv
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
    #
    csn
    cN
    cfv
    cM
    cfv
    @3
    cS
    cfv
    #
    csn
    #
    cL
    cfv
    @1
    @2
    cS
    cfv
    c.pb
    co
    #
    csn
    #
    cL
    cfv
    hdmaprnlem1.pt
    wph
    cC
    cS
    @3
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
    wph
    cU
    clmod
    wcel
    @0
    cV
    wcel
    @2
    cV
    wcel
    @3
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.k
    dvhlmod
    hdmaprnlem1.ue
    wph
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
    hdmaprnlem1.t2
    hdmaprnlem4tN
    #
    c.pl
    cV
    cU
    @0
    @2
    hdmaprnlem1.v
    hdmaprnlem1.p
    lmodvacl
    syl3anc
    hdmap10
    wph
    @5
    @7
    cL
    wph
    @4
    @6
    wph
    cC
    c.pl
    c.pb
    cS
    cU
    cH
    cK
    cV
    cW
    @0
    @2
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.v
    hdmaprnlem1.p
    hdmaprnlem1.c
    hdmaprnlem1.a
    hdmaprnlem1.s
    hdmaprnlem1.k
    hdmaprnlem1.ue
    @8
    hdmapadd
    sneqd
    fveq2d
    3eqtrd
end
