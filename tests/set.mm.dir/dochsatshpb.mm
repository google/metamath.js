include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "dochsatshp.mm"
include "cv.mm"
include "c0g.mm"
include "wne.mm"
include "wrex.mm"
include "csn.mm"
include "cbs.mm"
include "wceq.mm"
include "cdih.mm"
include "crn.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
include "syl.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lshpne.mm"
include "eqnetrd.mm"
include "wb.mm"
include "dochssv.mm"
include "dochn0nv.mm"
include "mpbird.mm"
include "dochlss.mm"
include "lssne0.mm"
include "mpbid.mm"
include "w3a.mm"
include "clspn.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "lspsnel5a.mm"
include "lssel.mm"
include "dihlsprn.mm"
include "dochord.mm"
include "eqsstr3d.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "simp1r.mm"
include "simp3.mm"
include "lsatlspsn2.mm"
include "syl3anc.mm"
include "lshpcmp.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "dochsat.mm"
include "impbida.mm"

theorem dochsatshpb
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cY: class Y
  let vv: setvar v
  assume dochsatshpb.h: |- H = ( LHyp ` K )
  assume dochsatshpb.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsatshpb.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsatshpb.s: |- S = ( LSubSp ` U )
  assume dochsatshpb.a: |- A = ( LSAtoms ` U )
  assume dochsatshpb.y: |- Y = ( LSHyp ` U )
  assume dochsatshpb.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsatshpb.q: |- ( ph -> Q e. S )


  assert |- ( ph -> ( Q e. A <-> ( ._|_ ` Q ) e. Y ) )

  proof
    wph
    cQ
    cA
    wcel
    #
    cQ
    c.pe
    cfv
    #
    cY
    wcel
    #
    wph
    @0
    wa
    cA
    cQ
    cU
    cH
    cK
    c.pe
    cW
    cY
    dochsatshpb.h
    dochsatshpb.u
    dochsatshpb.o
    dochsatshpb.a
    dochsatshpb.y
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @0
    dochsatshpb.k
    adantr
    wph
    @0
    simpr
    dochsatshp
    wph
    @2
    wa
    #
    @1
    c.pe
    cfv
    #
    cA
    wcel
    #
    @0
    @4
    vv
    cv
    #
    cU
    c0g
    cfv
    #
    wne
    #
    vv
    @5
    wrex
    #
    @6
    @4
    @5
    @8
    csn
    wne
    #
    @10
    @4
    @11
    @5
    c.pe
    cfv
    #
    cU
    cbs
    cfv
    #
    wne
    #
    @4
    @12
    @1
    @13
    wph
    @12
    @1
    wceq
    #
    @2
    wph
    @3
    @1
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    wcel
    #
    @15
    dochsatshpb.k
    wph
    @3
    cQ
    @13
    wss
    #
    @18
    dochsatshpb.k
    wph
    cQ
    cS
    wcel
    #
    @19
    dochsatshpb.q
    cS
    cQ
    @13
    cU
    @13
    eqid
    #
    dochsatshpb.s
    lssss
    syl
    #
    cU
    cH
    @16
    cK
    c.pe
    @13
    cW
    cQ
    dochsatshpb.h
    @16
    eqid
    #
    dochsatshpb.u
    @21
    dochsatshpb.o
    dochcl
    syl2anc
    #
    cH
    @16
    cK
    c.pe
    cW
    @1
    dochsatshpb.h
    @23
    dochsatshpb.o
    dochoc
    #
    syl2anc
    adantr
    @4
    @1
    cY
    @13
    cU
    @21
    dochsatshpb.y
    wph
    cU
    clmod
    wcel
    #
    @2
    wph
    cU
    cH
    cK
    cW
    dochsatshpb.h
    dochsatshpb.u
    dochsatshpb.k
    dvhlmod
    adantr
    #
    wph
    @2
    simpr
    lshpne
    eqnetrd
    wph
    @11
    @14
    wb
    @2
    wph
    cU
    cH
    cK
    c.pe
    @13
    cW
    @1
    @8
    dochsatshpb.h
    dochsatshpb.o
    dochsatshpb.u
    @21
    @8
    eqid
    #
    dochsatshpb.k
    wph
    @3
    @19
    @1
    @13
    wss
    #
    dochsatshpb.k
    @22
    cU
    cH
    cK
    c.pe
    @13
    cW
    cQ
    dochsatshpb.h
    dochsatshpb.u
    @21
    dochsatshpb.o
    dochssv
    syl2anc
    dochn0nv
    adantr
    mpbird
    @4
    @5
    cS
    wcel
    #
    @11
    @10
    wb
    wph
    @30
    @2
    wph
    @3
    @29
    @30
    dochsatshpb.k
    wph
    @1
    cS
    wcel
    #
    @29
    wph
    @3
    @19
    @31
    dochsatshpb.k
    @22
    cS
    cU
    cH
    cK
    c.pe
    @13
    cW
    cQ
    dochsatshpb.h
    dochsatshpb.u
    @21
    dochsatshpb.s
    dochsatshpb.o
    dochlss
    syl2anc
    cS
    @1
    @13
    cU
    @21
    dochsatshpb.s
    lssss
    syl
    #
    cS
    cU
    cH
    cK
    c.pe
    @13
    cW
    @1
    dochsatshpb.h
    dochsatshpb.u
    @21
    dochsatshpb.s
    dochsatshpb.o
    dochlss
    syl2anc
    adantr
    #
    vv
    cS
    cU
    @5
    @8
    @28
    dochsatshpb.s
    lssne0
    syl
    mpbid
    @4
    @9
    @6
    vv
    @5
    @4
    @7
    @5
    wcel
    #
    @9
    w3a
    #
    @5
    @7
    csn
    cU
    clspn
    cfv
    #
    cfv
    #
    cA
    @35
    @5
    @37
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @37
    @35
    @1
    @38
    c.pe
    @35
    @1
    @38
    wss
    @1
    @38
    wceq
    @35
    @1
    @12
    @38
    @35
    @3
    @18
    @15
    @4
    @34
    @3
    @9
    wph
    @3
    @2
    dochsatshpb.k
    adantr
    #
    3ad2ant1
    #
    @4
    @34
    @18
    @9
    wph
    @18
    @2
    @24
    adantr
    3ad2ant1
    @25
    syl2anc
    @35
    @37
    @5
    wss
    @12
    @38
    wss
    @35
    cS
    @5
    @36
    cU
    @7
    dochsatshpb.s
    @36
    eqid
    #
    @4
    @34
    @26
    @9
    @27
    3ad2ant1
    #
    @4
    @34
    @30
    @9
    @33
    3ad2ant1
    #
    @4
    @34
    @9
    simp2
    #
    lspsnel5a
    @35
    cH
    @16
    cK
    c.pe
    cW
    @37
    @5
    dochsatshpb.h
    @23
    dochsatshpb.o
    @41
    @35
    @3
    @7
    @13
    wcel
    #
    @37
    @17
    wcel
    #
    @41
    @35
    @30
    @34
    @46
    @44
    @45
    cS
    @5
    @13
    cU
    @7
    @21
    dochsatshpb.s
    lssel
    syl2anc
    #
    cU
    cH
    @16
    cK
    @36
    @13
    cW
    @7
    dochsatshpb.h
    dochsatshpb.u
    @21
    @42
    @23
    dihlsprn
    syl2anc
    #
    @4
    @34
    @5
    @17
    wcel
    #
    @9
    wph
    @50
    @2
    wph
    @3
    @29
    @50
    dochsatshpb.k
    @32
    cU
    cH
    @16
    cK
    c.pe
    @13
    cW
    @1
    dochsatshpb.h
    @23
    dochsatshpb.u
    @21
    dochsatshpb.o
    dochcl
    syl2anc
    adantr
    3ad2ant1
    dochord
    mpbid
    eqsstr3d
    @35
    @1
    @38
    cY
    cU
    dochsatshpb.y
    @4
    @34
    cU
    clvec
    wcel
    #
    @9
    wph
    @51
    @2
    wph
    cU
    cH
    cK
    cW
    dochsatshpb.h
    dochsatshpb.u
    dochsatshpb.k
    dvhlvec
    adantr
    3ad2ant1
    wph
    @2
    @34
    @9
    simp1r
    @35
    cA
    @37
    cU
    cH
    cK
    c.pe
    cW
    cY
    dochsatshpb.h
    dochsatshpb.u
    dochsatshpb.o
    dochsatshpb.a
    dochsatshpb.y
    @41
    @35
    @26
    @46
    @9
    @37
    cA
    wcel
    @43
    @48
    @4
    @34
    @9
    simp3
    cA
    @36
    @13
    cU
    @7
    @8
    @21
    @42
    @28
    dochsatshpb.a
    lsatlspsn2
    syl3anc
    #
    dochsatshp
    lshpcmp
    mpbid
    fveq2d
    @35
    @3
    @47
    @39
    @37
    wceq
    @41
    @49
    cH
    @16
    cK
    c.pe
    cW
    @37
    dochsatshpb.h
    @23
    dochsatshpb.o
    dochoc
    syl2anc
    eqtrd
    @52
    eqeltrd
    rexlimdv3a
    mpd
    @4
    cA
    cQ
    cS
    cU
    cH
    cK
    c.pe
    cW
    dochsatshpb.h
    dochsatshpb.o
    dochsatshpb.u
    dochsatshpb.s
    dochsatshpb.a
    @40
    wph
    @20
    @2
    dochsatshpb.q
    adantr
    dochsat
    mpbid
    impbida
end
