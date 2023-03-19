include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "wne.mm"
include "lcdlmod.mm"
include "clmod.mm"
include "wcel.mm"
include "hdmapcl.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "clss.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lspsnid.mm"
include "lcdlvec.mm"
include "dvhlmod.mm"
include "lssneln0.mm"
include "hdmapnzcl.mm"
include "hdmaprnlem1N.mm"
include "lspsnne1.mm"
include "lssvancl2.mm"
include "lspsnne2.mm"
include "necomd.mm"
include "crn.mm"
include "mapdrn2.mm"
include "eleqtrrd.mm"
include "mapdcnvid2.mm"
include "3netr4d.mm"
include "mapdcnvcl.mm"
include "mapd11.mm"
include "necon3bid.mm"
include "mpbid.mm"

theorem hdmaprnlem3N
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
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


  assert |- ( ph -> ( N ` { v } ) =/= ( `' M ` ( L ` { ( ( S ` u ) .+b s ) } ) ) )

  proof
    wph
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
    csn
    cL
    cfv
    #
    cM
    ccnv
    cfv
    #
    cM
    cfv
    #
    wne
    @1
    @8
    wne
    wph
    @5
    csn
    cL
    cfv
    #
    @7
    @2
    @9
    wph
    @7
    @10
    wph
    cL
    cD
    cC
    @6
    @5
    hdmaprnlem1.d
    hdmaprnlem1.l
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
    clmod
    wcel
    #
    @4
    cD
    wcel
    @5
    cD
    wcel
    #
    @6
    cD
    wcel
    #
    @11
    wph
    cC
    cD
    cS
    @3
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
    @5
    cD
    cQ
    csn
    hdmaprnlem1.se
    eldifad
    #
    c.pb
    cD
    cC
    @4
    @5
    hdmaprnlem1.d
    hdmaprnlem1.a
    lmodvacl
    syl3anc
    #
    @16
    wph
    c.pb
    cC
    clss
    cfv
    #
    @10
    cD
    cC
    @5
    @4
    hdmaprnlem1.d
    hdmaprnlem1.a
    @18
    eqid
    #
    @11
    wph
    @12
    @13
    @10
    @18
    wcel
    @11
    @16
    @18
    cL
    cD
    cC
    @5
    hdmaprnlem1.d
    @19
    hdmaprnlem1.l
    lspsncl
    syl2anc
    wph
    @12
    @13
    @5
    @10
    wcel
    @11
    @16
    cL
    cD
    cC
    @5
    hdmaprnlem1.d
    hdmaprnlem1.l
    lspsnid
    syl2anc
    @15
    wph
    cL
    cD
    cC
    @4
    @5
    cQ
    hdmaprnlem1.d
    hdmaprnlem1.q
    hdmaprnlem1.l
    wph
    cC
    cH
    cK
    cW
    hdmaprnlem1.h
    hdmaprnlem1.c
    hdmaprnlem1.k
    lcdlvec
    wph
    cC
    cD
    cQ
    cS
    @3
    cU
    cH
    cK
    cV
    cW
    c.0
    hdmaprnlem1.h
    hdmaprnlem1.u
    hdmaprnlem1.v
    hdmaprnlem1.o
    hdmaprnlem1.c
    hdmaprnlem1.q
    hdmaprnlem1.d
    hdmaprnlem1.s
    hdmaprnlem1.k
    wph
    cU
    clss
    cfv
    #
    @1
    cV
    cU
    @3
    c.0
    hdmaprnlem1.v
    hdmaprnlem1.o
    @20
    eqid
    #
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
    @0
    cV
    wcel
    @1
    @20
    wcel
    @22
    hdmaprnlem1.ve
    @20
    cN
    cV
    cU
    @0
    hdmaprnlem1.v
    @21
    hdmaprnlem1.n
    lspsncl
    syl2anc
    #
    hdmaprnlem1.ue
    hdmaprnlem1.un
    lssneln0
    hdmapnzcl
    @16
    wph
    vv
    vu
    cC
    cD
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
    hdmaprnlem1N
    lspsnne1
    lssvancl2
    lspsnne2
    necomd
    hdmaprnlem1.e
    wph
    cH
    cK
    cM
    cW
    @7
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.k
    wph
    @7
    @18
    cM
    crn
    wph
    @12
    @14
    @7
    @18
    wcel
    @11
    @17
    @18
    cL
    cD
    cC
    @6
    hdmaprnlem1.d
    @19
    hdmaprnlem1.l
    lspsncl
    syl2anc
    wph
    cC
    @18
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.c
    @19
    hdmaprnlem1.k
    mapdrn2
    eleqtrrd
    #
    mapdcnvid2
    3netr4d
    wph
    @2
    @9
    @1
    @8
    wph
    @20
    cU
    cH
    cK
    cM
    cW
    @1
    @8
    hdmaprnlem1.h
    hdmaprnlem1.u
    @21
    hdmaprnlem1.m
    hdmaprnlem1.k
    @23
    wph
    @20
    cU
    cH
    cK
    cM
    cW
    @7
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @21
    hdmaprnlem1.k
    @24
    mapdcnvcl
    mapd11
    necon3bid
    mpbid
end
