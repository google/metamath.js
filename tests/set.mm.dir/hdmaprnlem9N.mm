include "cv.mm"
include "cfv.mm"
include "csg.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "wcel.mm"
include "cin.mm"
include "hdmaprnlem7N.mm"
include "hdmaprnlem8N.mm"
include "hdmaprnlem4N.mm"
include "eleqtrd.mm"
include "elind.mm"
include "lcdlvec.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "hdmapcl.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "ccnv.mm"
include "wne.mm"
include "clss.mm"
include "crn.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdrn2.mm"
include "eleqtrrd.mm"
include "mapdcnvid2.mm"
include "eqtr4d.mm"
include "dvhlmod.mm"
include "mapdcnvcl.mm"
include "mapd11.mm"
include "mpbid.mm"
include "hdmaprnlem3N.mm"
include "eqnetrrd.mm"
include "mapdcnv11N.mm"
include "necon3bid.mm"
include "necomd.mm"
include "lspdisj2.mm"
include "elsni.mm"
include "syl.mm"
include "wb.mm"
include "hdmaprnlem4tN.mm"
include "lmodsubeq0.mm"

theorem hdmaprnlem9N
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


  assert |- ( ph -> s = ( S ` t ) )

  proof
    wph
    vs
    cv
    #
    vt
    cv
    #
    cS
    cfv
    #
    cC
    csg
    cfv
    #
    co
    #
    cQ
    wceq
    #
    @0
    @2
    wceq
    #
    wph
    @4
    cQ
    csn
    #
    wcel
    @5
    wph
    @4
    vu
    cv
    #
    cS
    cfv
    #
    @0
    c.pb
    co
    #
    csn
    cL
    cfv
    #
    @0
    csn
    cL
    cfv
    #
    cin
    @7
    wph
    @11
    @12
    @4
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
    hdmaprnlem7N
    wph
    @4
    @1
    csn
    cN
    cfv
    cM
    cfv
    @12
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
    hdmaprnlem8N
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
    eleqtrd
    elind
    wph
    cL
    cD
    cC
    @10
    @0
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
    clmod
    wcel
    #
    @9
    cD
    wcel
    @0
    cD
    wcel
    #
    @10
    cD
    wcel
    #
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
    cD
    cS
    @8
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
    wph
    @0
    cD
    @7
    hdmaprnlem1.se
    eldifad
    #
    c.pb
    cD
    cC
    @9
    @0
    hdmaprnlem1.d
    hdmaprnlem1.a
    lmodvacl
    syl3anc
    #
    @17
    wph
    @12
    @11
    wph
    @12
    cM
    ccnv
    #
    cfv
    #
    @11
    @19
    cfv
    #
    wne
    @12
    @11
    wne
    wph
    vv
    cv
    #
    csn
    cN
    cfv
    #
    @20
    @21
    wph
    @23
    cM
    cfv
    #
    @20
    cM
    cfv
    #
    wceq
    @23
    @20
    wceq
    wph
    @24
    @12
    @25
    hdmaprnlem1.e
    wph
    cH
    cK
    cM
    cW
    @12
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.k
    wph
    @12
    cC
    clss
    cfv
    #
    cM
    crn
    #
    wph
    @13
    @14
    @12
    @26
    wcel
    @16
    @17
    @26
    cL
    cD
    cC
    @0
    hdmaprnlem1.d
    @26
    eqid
    #
    hdmaprnlem1.l
    lspsncl
    syl2anc
    wph
    cC
    @26
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.c
    @28
    hdmaprnlem1.k
    mapdrn2
    #
    eleqtrrd
    #
    mapdcnvid2
    eqtr4d
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
    @23
    @20
    hdmaprnlem1.h
    hdmaprnlem1.u
    @31
    eqid
    #
    hdmaprnlem1.m
    hdmaprnlem1.k
    wph
    cU
    clmod
    wcel
    @22
    cV
    wcel
    @23
    @31
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
    hdmaprnlem1.ve
    @31
    cN
    cV
    cU
    @22
    hdmaprnlem1.v
    @32
    hdmaprnlem1.n
    lspsncl
    syl2anc
    wph
    @31
    cU
    cH
    cK
    cM
    cW
    @12
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @32
    hdmaprnlem1.k
    @30
    mapdcnvcl
    mapd11
    mpbid
    wph
    vv
    vu
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
    hdmaprnlem3N
    eqnetrrd
    wph
    @20
    @21
    @12
    @11
    wph
    cH
    cK
    cM
    cW
    @12
    @11
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.k
    @30
    wph
    @11
    @26
    @27
    wph
    @13
    @15
    @11
    @26
    wcel
    @16
    @18
    @26
    cL
    cD
    cC
    @10
    hdmaprnlem1.d
    @28
    hdmaprnlem1.l
    lspsncl
    syl2anc
    @29
    eleqtrrd
    mapdcnv11N
    necon3bid
    mpbid
    necomd
    lspdisj2
    eleqtrd
    @4
    cQ
    elsni
    syl
    wph
    @13
    @14
    @2
    cD
    wcel
    @5
    @6
    wb
    @16
    @17
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
    @0
    @2
    @3
    cD
    cC
    cQ
    hdmaprnlem1.d
    hdmaprnlem1.q
    @3
    eqid
    lmodsubeq0
    syl3anc
    mpbid
end
