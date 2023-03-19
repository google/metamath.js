include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "ccnv.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "clsa.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "lcdlmod.mm"
include "wcel.mm"
include "wne.mm"
include "clmod.mm"
include "hdmapcl.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "hdmaprnlem1N.mm"
include "lmodindp1.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lsatlspsn.mm"
include "mapdcnvatN.mm"
include "hdmaprnlem3uN.mm"
include "necomd.mm"
include "hdmaprnlem3N.mm"
include "clsm.mm"
include "cpr.mm"
include "wss.mm"
include "clss.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdcl2.mm"
include "lsmcl.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "lspsnid.mm"
include "hdmap10.mm"
include "eleqtrrd.mm"
include "eqimss2.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "lspsnel5a.mm"
include "mapdlsm.mm"
include "sseqtr4d.mm"
include "crn.mm"
include "mapdrn2.mm"
include "mapdcl.mm"
include "mapdcnvordN.mm"
include "lsmpr.mm"
include "mapdcnvid1N.mm"
include "eqtr4d.mm"
include "lsatfixedN.mm"
include "wa.mm"
include "simpr.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "wn.mm"
include "simplr.mm"
include "hdmaprnlem4tN.mm"
include "mapdcnv11N.mm"
include "mpbid.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem hdmaprnlem3eN
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
  assert |- ( ph -> E. t e. ( ( N ` { v } ) \ { .0. } ) ( L ` { ( ( S ` u ) .+b s ) } ) = ( M ` ( N ` { ( u .+ t ) } ) ) )

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
    csn
    cL
    cfv
    #
    cM
    ccnv
    #
    cfv
    #
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
    #
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
    @4
    @9
    cM
    cfv
    #
    wceq
    #
    vt
    @13
    wrex
    wph
    vt
    cU
    clsa
    cfv
    #
    c.pl
    @6
    cN
    cV
    cU
    @0
    @11
    c.0
    hdmaprnlem1.v
    hdmaprnlem3e.p
    hdmaprnlem1.o
    hdmaprnlem1.n
    @16
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
    dvhlvec
    wph
    @16
    cC
    clsa
    cfv
    #
    cC
    @4
    cU
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @17
    hdmaprnlem1.c
    @18
    eqid
    #
    hdmaprnlem1.k
    wph
    @18
    cL
    cD
    cC
    @3
    cQ
    hdmaprnlem1.d
    hdmaprnlem1.l
    hdmaprnlem1.q
    @19
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
    @3
    cD
    wcel
    #
    @3
    cQ
    wne
    @3
    cD
    cQ
    csn
    #
    cdif
    #
    wcel
    wph
    cC
    clmod
    wcel
    #
    @1
    cD
    wcel
    #
    @2
    cD
    wcel
    @21
    @20
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
    @22
    hdmaprnlem1.se
    eldifad
    #
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
    wph
    c.pb
    cL
    cD
    cC
    @1
    @2
    cQ
    hdmaprnlem1.d
    hdmaprnlem1.a
    hdmaprnlem1.q
    hdmaprnlem1.l
    @20
    @26
    @27
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
    lmodindp1
    @3
    cD
    cQ
    eldifsn
    sylanbrc
    lsatlspsn
    mapdcnvatN
    hdmaprnlem1.ue
    hdmaprnlem1.ve
    wph
    @0
    csn
    cN
    cfv
    #
    @6
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
    hdmaprnlem3uN
    necomd
    wph
    @12
    @6
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
    necomd
    wph
    @6
    @29
    @12
    cU
    clsm
    cfv
    #
    co
    #
    cM
    cfv
    #
    @5
    cfv
    #
    @0
    @11
    cpr
    cN
    cfv
    #
    wph
    @6
    @33
    wss
    @4
    @32
    wss
    wph
    @4
    @29
    cM
    cfv
    #
    @12
    cM
    cfv
    #
    cC
    clsm
    cfv
    #
    co
    #
    @32
    wph
    cC
    clss
    cfv
    #
    @38
    cL
    cC
    @3
    @39
    eqid
    #
    hdmaprnlem1.l
    @20
    wph
    @24
    @35
    @39
    wcel
    @36
    @39
    wcel
    @38
    @39
    wcel
    @20
    wph
    cC
    @29
    cU
    clss
    cfv
    #
    @39
    cU
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @41
    eqid
    #
    hdmaprnlem1.c
    @40
    hdmaprnlem1.k
    wph
    cU
    clmod
    wcel
    #
    @0
    cV
    wcel
    #
    @29
    @41
    wcel
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
    hdmaprnlem1.ue
    @41
    cN
    cV
    cU
    @0
    hdmaprnlem1.v
    @42
    hdmaprnlem1.n
    lspsncl
    syl2anc
    #
    mapdcl2
    #
    wph
    cC
    @12
    @41
    @39
    cU
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @42
    hdmaprnlem1.c
    @40
    hdmaprnlem1.k
    wph
    @43
    @11
    cV
    wcel
    #
    @12
    @41
    wcel
    #
    @46
    hdmaprnlem1.ve
    @41
    cN
    cV
    cU
    @11
    hdmaprnlem1.v
    @42
    hdmaprnlem1.n
    lspsncl
    syl2anc
    #
    mapdcl2
    #
    @37
    @39
    @35
    @36
    cC
    @40
    @37
    eqid
    #
    lsmcl
    syl3anc
    wph
    @35
    cC
    csubg
    cfv
    #
    wcel
    @36
    @54
    wcel
    @1
    @35
    wcel
    @2
    @36
    wcel
    #
    @3
    @38
    wcel
    wph
    @39
    @54
    @35
    wph
    @24
    @39
    @54
    wss
    @20
    @39
    cC
    @40
    lsssssubg
    syl
    #
    @48
    sseldd
    wph
    @39
    @54
    @36
    @56
    @52
    sseldd
    wph
    @1
    @1
    csn
    cL
    cfv
    #
    @35
    wph
    @24
    @25
    @1
    @57
    wcel
    @20
    @26
    cL
    cD
    cC
    @1
    hdmaprnlem1.d
    hdmaprnlem1.l
    lspsnid
    syl2anc
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
    eleqtrrd
    wph
    @55
    @2
    csn
    cL
    cfv
    #
    @36
    wss
    #
    wph
    @36
    @58
    wceq
    #
    @59
    hdmaprnlem1.e
    @58
    @36
    eqimss2
    syl
    wph
    @39
    @36
    cL
    cD
    cC
    @2
    hdmaprnlem1.d
    @40
    hdmaprnlem1.l
    @20
    @52
    @27
    lspsnel5
    mpbird
    c.pb
    @37
    @35
    @36
    cC
    @1
    @2
    hdmaprnlem1.a
    @53
    lsmelvali
    syl22anc
    lspsnel5a
    wph
    cC
    @37
    @30
    @41
    cU
    cH
    cK
    cM
    cW
    @29
    @12
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @42
    @30
    eqid
    #
    hdmaprnlem1.c
    @53
    hdmaprnlem1.k
    @47
    @51
    mapdlsm
    sseqtr4d
    wph
    cH
    cK
    cM
    cW
    @4
    @32
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.k
    wph
    @4
    @39
    cM
    crn
    #
    wph
    @24
    @21
    @4
    @39
    wcel
    @20
    @28
    @39
    cL
    cD
    cC
    @3
    hdmaprnlem1.d
    @40
    hdmaprnlem1.l
    lspsncl
    syl2anc
    wph
    cC
    @39
    cH
    cK
    cM
    cW
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.c
    @40
    hdmaprnlem1.k
    mapdrn2
    eleqtrrd
    #
    wph
    @41
    cU
    cH
    cK
    cM
    cW
    @31
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @42
    hdmaprnlem1.k
    wph
    @43
    @45
    @50
    @31
    @41
    wcel
    @46
    @47
    @51
    @30
    @41
    @29
    @12
    cU
    @42
    @61
    lsmcl
    syl3anc
    #
    mapdcl
    mapdcnvordN
    mpbird
    wph
    @34
    @31
    @33
    wph
    @30
    cN
    cV
    cU
    @0
    @11
    hdmaprnlem1.v
    hdmaprnlem1.n
    @61
    @46
    hdmaprnlem1.ue
    hdmaprnlem1.ve
    lsmpr
    wph
    @41
    cU
    cH
    cK
    cM
    cW
    @31
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @42
    hdmaprnlem1.k
    @64
    mapdcnvid1N
    eqtr4d
    sseqtr4d
    lsatfixedN
    wph
    @10
    @15
    vt
    @13
    wph
    @7
    @13
    wcel
    #
    wa
    #
    @10
    @15
    @66
    @10
    wa
    #
    @6
    @14
    @5
    cfv
    #
    wceq
    @15
    @67
    @6
    @9
    @68
    @66
    @10
    simpr
    @67
    @41
    cU
    cH
    cK
    cM
    cW
    @9
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @42
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @65
    @10
    hdmaprnlem1.k
    ad2antrr
    #
    @67
    @43
    @8
    cV
    wcel
    #
    @9
    @41
    wcel
    wph
    @43
    @65
    @10
    @46
    ad2antrr
    #
    @67
    @43
    @44
    @7
    cV
    wcel
    @70
    @71
    wph
    @44
    @65
    @10
    hdmaprnlem1.ue
    ad2antrr
    #
    @67
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
    @69
    wph
    @2
    @23
    wcel
    @65
    @10
    hdmaprnlem1.se
    ad2antrr
    wph
    @49
    @65
    @10
    hdmaprnlem1.ve
    ad2antrr
    wph
    @60
    @65
    @10
    hdmaprnlem1.e
    ad2antrr
    @72
    wph
    @0
    @12
    wcel
    wn
    @65
    @10
    hdmaprnlem1.un
    ad2antrr
    hdmaprnlem1.d
    hdmaprnlem1.q
    hdmaprnlem1.o
    hdmaprnlem1.a
    wph
    @65
    @10
    simplr
    hdmaprnlem4tN
    c.pl
    cV
    cU
    @0
    @7
    hdmaprnlem1.v
    hdmaprnlem3e.p
    lmodvacl
    syl3anc
    @41
    cN
    cV
    cU
    @8
    hdmaprnlem1.v
    @42
    hdmaprnlem1.n
    lspsncl
    syl2anc
    #
    mapdcnvid1N
    eqtr4d
    @67
    cH
    cK
    cM
    cW
    @4
    @14
    hdmaprnlem1.h
    hdmaprnlem1.m
    @69
    wph
    @4
    @62
    wcel
    @65
    @10
    @63
    ad2antrr
    @67
    @41
    cU
    cH
    cK
    cM
    cW
    @9
    hdmaprnlem1.h
    hdmaprnlem1.m
    hdmaprnlem1.u
    @42
    @69
    @73
    mapdcl
    mapdcnv11N
    mpbid
    ex
    reximdva
    mpd
end
