include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "ccnv.mm"
include "co.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdcnvid1N.mm"
include "wne.mm"
include "hdmap10.mm"
include "lcdlvec.mm"
include "hdmapcl.mm"
include "hdmaprnlem1N.mm"
include "lspindp3.mm"
include "eqnetrd.mm"
include "mapdcl.mm"
include "crn.mm"
include "lcdlmod.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "mapdrn2.mm"
include "eleqtrrd.mm"
include "mapdcnv11N.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eqnetrrd.mm"

theorem hdmaprnlem3uN
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


  assert |- ( ph -> ( N ` { u } ) =/= ( `' M ` ( L ` { ( ( S ` u ) .+b s ) } ) ) )

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
    cM
    ccnv
    #
    cfv
    #
    @1
    @0
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
    @3
    cfv
    #
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
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @10
    eqid
    #
    hdmaprnlem1.k
    wph
    cU
    clmod
    wcel
    @0
    cV
    wcel
    @1
    @10
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
    @10
    cN
    cV
    cU
    @0
    hdmaprnlem1.v
    @11
    hdmaprnlem1.n
    lspsncl
    syl2anc
    #
    mapdcnvid1N
    wph
    @4
    @9
    wne
    @2
    @8
    wne
    wph
    @2
    @5
    csn
    cL
    cfv
    @8
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
    wph
    c.pb
    cL
    cD
    cC
    @5
    @6
    cQ
    hdmaprnlem1.d
    hdmaprnlem1.a
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
    hdmaprnlem1.se
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
    lspindp3
    eqnetrd
    wph
    @4
    @9
    @2
    @8
    wph
    cH
    cK
    cM
    cW
    @2
    @8
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.k
    wph
    @10
    cU
    cH
    cK
    cM
    cW
    @1
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @11
    hdmaprnlem1.k
    @12
    mapdcl
    wph
    @8
    cC
    clss
    cfv
    #
    cM
    crn
    wph
    cC
    clmod
    wcel
    #
    @7
    cD
    wcel
    #
    @8
    @14
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
    @15
    @5
    cD
    wcel
    @6
    cD
    wcel
    @16
    @17
    @13
    wph
    @6
    cD
    cQ
    csn
    hdmaprnlem1.se
    eldifad
    c.pb
    cD
    cC
    @5
    @6
    hdmaprnlem1.d
    hdmaprnlem1.a
    lmodvacl
    syl3anc
    @14
    cL
    cD
    cC
    @7
    hdmaprnlem1.d
    @14
    eqid
    #
    hdmaprnlem1.l
    lspsncl
    syl2anc
    wph
    cC
    @14
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.c
    @18
    hdmaprnlem1.k
    mapdrn2
    eleqtrrd
    mapdcnv11N
    necon3bid
    mpbird
    eqnetrrd
end
