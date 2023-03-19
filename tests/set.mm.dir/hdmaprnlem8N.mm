include "clmod.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "clss.mm"
include "csg.mm"
include "co.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "hdmaprnlem4tN.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdcl2.mm"
include "eldifad.mm"
include "lspsnid.mm"
include "hdmaprnlem4N.mm"
include "eleqtrrd.mm"
include "hdmapcl.mm"
include "hdmap10.mm"
include "lssvsubcl.mm"
include "syl22anc.mm"

theorem hdmaprnlem8N
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


  assert |- ( ph -> ( s ( -g ` C ) ( S ` t ) ) e. ( M ` ( N ` { t } ) ) )

  proof
    wph
    cC
    clmod
    wcel
    #
    vt
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cC
    clss
    cfv
    #
    wcel
    vs
    cv
    #
    @3
    wcel
    @1
    cS
    cfv
    #
    @3
    wcel
    @5
    @6
    cC
    csg
    cfv
    #
    co
    @3
    wcel
    wph
    cC
    cH
    cK
    cW
    hdmaprnlem1.h
    hdmaprnlem1.c
    hdmaprnlem1.k
    lcdlmod
    #
    wph
    cC
    @2
    cU
    clss
    cfv
    #
    @4
    cU
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @9
    eqid
    #
    hdmaprnlem1.c
    @4
    eqid
    #
    hdmaprnlem1.k
    wph
    cU
    clmod
    wcel
    @1
    cV
    wcel
    @2
    @9
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
    @9
    cN
    cV
    cU
    @1
    hdmaprnlem1.v
    @10
    hdmaprnlem1.n
    lspsncl
    syl2anc
    mapdcl2
    wph
    @5
    @5
    csn
    cL
    cfv
    #
    @3
    wph
    @0
    @5
    cD
    wcel
    @5
    @13
    wcel
    @8
    wph
    @5
    cD
    cQ
    csn
    hdmaprnlem1.se
    eldifad
    cL
    cD
    cC
    @5
    hdmaprnlem1.d
    hdmaprnlem1.l
    lspsnid
    syl2anc
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
    hdmaprnlem4N
    eleqtrrd
    wph
    @6
    @6
    csn
    cL
    cfv
    #
    @3
    wph
    @0
    @6
    cD
    wcel
    @6
    @14
    wcel
    @8
    wph
    cC
    cD
    cS
    @1
    cU
    cH
    cK
    cV
    cW
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.v
    hdmaprnlem1.c
    hdmaprnlem1.d
    hdmaprnlem1.s
    hdmaprnlem1.k
    @12
    hdmapcl
    cL
    cD
    cC
    @6
    hdmaprnlem1.d
    hdmaprnlem1.l
    lspsnid
    syl2anc
    wph
    cC
    cS
    @1
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
    @12
    hdmap10
    eleqtrrd
    @4
    @3
    @7
    cC
    @5
    @6
    @7
    eqid
    @11
    lssvsubcl
    syl22anc
end
