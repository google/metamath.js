include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csg.mm"
include "csn.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "cabl.mm"
include "lcdlmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "hdmapcl.mm"
include "eldifad.mm"
include "hdmaprnlem4tN.mm"
include "ablpnpcan.mm"
include "clss.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lspsnid.mm"
include "hdmaprnlem6N.mm"
include "eleqtrrd.mm"
include "lssvsubcl.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"

theorem hdmaprnlem7N
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


  assert |- ( ph -> ( s ( -g ` C ) ( S ` t ) ) e. ( L ` { ( ( S ` u ) .+b s ) } ) )

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
    #
    c.pb
    co
    #
    @1
    vt
    cv
    #
    cS
    cfv
    #
    c.pb
    co
    #
    cC
    csg
    cfv
    #
    co
    #
    @2
    @5
    @7
    co
    @3
    csn
    cL
    cfv
    #
    wph
    cD
    c.pb
    cC
    @7
    @1
    @2
    @5
    hdmaprnlem1.d
    hdmaprnlem1.a
    @7
    eqid
    #
    wph
    cC
    clmod
    wcel
    #
    cC
    cabl
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
    cC
    lmodabl
    syl
    #
    wph
    cC
    cD
    cS
    @0
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
    hdmaprnlem1.ue
    hdmapcl
    #
    wph
    @2
    cD
    cQ
    csn
    hdmaprnlem1.se
    eldifad
    #
    wph
    cC
    cD
    cS
    @4
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
    hdmapcl
    #
    @13
    @14
    @15
    @16
    ablpnpcan
    wph
    @11
    @9
    cC
    clss
    cfv
    #
    wcel
    #
    @3
    @9
    wcel
    #
    @6
    @9
    wcel
    @8
    @9
    wcel
    @12
    wph
    @11
    @3
    cD
    wcel
    #
    @18
    @12
    wph
    @11
    @1
    cD
    wcel
    #
    @2
    cD
    wcel
    @20
    @12
    @14
    @15
    c.pb
    cD
    cC
    @1
    @2
    hdmaprnlem1.d
    hdmaprnlem1.a
    lmodvacl
    syl3anc
    #
    @17
    cL
    cD
    cC
    @3
    hdmaprnlem1.d
    @17
    eqid
    #
    hdmaprnlem1.l
    lspsncl
    syl2anc
    wph
    @11
    @20
    @19
    @12
    @22
    cL
    cD
    cC
    @3
    hdmaprnlem1.d
    hdmaprnlem1.l
    lspsnid
    syl2anc
    wph
    @6
    @6
    csn
    cL
    cfv
    #
    @9
    wph
    @11
    @6
    cD
    wcel
    #
    @6
    @24
    wcel
    @12
    wph
    @11
    @21
    @5
    cD
    wcel
    @25
    @12
    @14
    @16
    c.pb
    cD
    cC
    @1
    @5
    hdmaprnlem1.d
    hdmaprnlem1.a
    lmodvacl
    syl3anc
    cL
    cD
    cC
    @6
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
    hdmaprnlem1.t2
    hdmaprnlem1.p
    hdmaprnlem1.pt
    hdmaprnlem6N
    eleqtrrd
    @17
    @9
    @7
    cC
    @3
    @6
    @10
    @23
    lssvsubcl
    syl22anc
    eqeltrrd
end
