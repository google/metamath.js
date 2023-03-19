include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "csn.mm"
include "wceq.mm"
include "cbs.mm"
include "cltrn.mm"
include "eqid.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "dvh3dim.mm"
include "w3a.mm"
include "csg.mm"
include "co.mm"
include "cotp.mm"
include "wa.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "cun.mm"
include "clss.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "lspprid1.mm"
include "lspsnel5a.mm"
include "lspprid2.mm"
include "unssd.mm"
include "sseld.mm"
include "con3dimp.mm"
include "3adant2.mm"
include "hdmapval2.mm"
include "eqcomd.mm"
include "clmod.mm"
include "simp3.mm"
include "lssneln0.mm"
include "c0g.mm"
include "hvmapcl2.mm"
include "mapdhvmap.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "cdif.mm"
include "hdmap1cl.mm"
include "hdmapcl.mm"
include "simprd.mm"
include "hdmap1eq.mm"
include "mpbii.mm"
include "mpbid.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmap10lem
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  assume hdmap10.h: |- H = ( LHyp ` K )
  assume hdmap10.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap10.v: |- V = ( Base ` U )
  assume hdmap10.n: |- N = ( LSpan ` U )
  assume hdmap10.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap10.l: |- L = ( LSpan ` C )
  assume hdmap10.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap10.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap10.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap10.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmap10.o: |- .0. = ( 0g ` U )
  assume hdmap10.d: |- D = ( Base ` C )
  assume hdmap10.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmap10.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap10lem.t: |- ( ph -> T e. ( V \ { .0. } ) )


  assert |- ( ph -> ( M ` ( N ` { T } ) ) = ( L ` { ( S ` T ) } ) )

  proof
    wph
    vx
    cv
    #
    cE
    cT
    cpr
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cV
    wrex
    cT
    csn
    cN
    cfv
    #
    cM
    cfv
    cT
    cS
    cfv
    #
    csn
    cL
    cfv
    wceq
    #
    wph
    vx
    cU
    cH
    cK
    cN
    cV
    cW
    cE
    cT
    hdmap10.h
    hdmap10.u
    hdmap10.v
    hdmap10.n
    hdmap10.k
    wph
    cE
    cV
    c.0
    csn
    #
    wph
    cK
    cbs
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cE
    cH
    cK
    cV
    cW
    c.0
    hdmap10.h
    @8
    eqid
    @9
    eqid
    hdmap10.u
    hdmap10.v
    hdmap10.o
    hdmap10.e
    hdmap10.k
    dvheveccl
    #
    eldifad
    #
    wph
    cT
    cV
    @7
    hdmap10lem.t
    eldifad
    #
    dvh3dim
    wph
    @3
    @6
    vx
    cV
    wph
    @0
    cV
    wcel
    #
    @3
    w3a
    #
    @6
    @0
    cT
    cU
    csg
    cfv
    #
    co
    csn
    cN
    cfv
    cM
    cfv
    cE
    cE
    cJ
    cfv
    #
    @0
    cotp
    cI
    cfv
    #
    @5
    cC
    csg
    cfv
    #
    co
    csn
    cL
    cfv
    wceq
    #
    @14
    @0
    @17
    cT
    cotp
    cI
    cfv
    #
    @5
    wceq
    @6
    @19
    wa
    @14
    @5
    @20
    @14
    cC
    cD
    cS
    cT
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    @0
    hdmap10.h
    hdmap10.e
    hdmap10.u
    hdmap10.v
    hdmap10.n
    hdmap10.c
    hdmap10.d
    hdmap10.j
    hdmap10.i
    hdmap10.s
    wph
    @13
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    hdmap10.k
    3ad2ant1
    #
    wph
    @13
    cT
    cV
    wcel
    @3
    @12
    3ad2ant1
    #
    wph
    @13
    @3
    simp2
    #
    wph
    @3
    @0
    cE
    csn
    cN
    cfv
    #
    @4
    cun
    #
    wcel
    #
    wn
    @13
    wph
    @26
    @2
    wph
    @25
    @1
    @0
    wph
    @24
    @4
    @1
    wph
    cU
    clss
    cfv
    #
    @1
    cN
    cU
    cE
    @27
    eqid
    #
    hdmap10.n
    wph
    cU
    cH
    cK
    cW
    hdmap10.h
    hdmap10.u
    hdmap10.k
    dvhlmod
    #
    wph
    @27
    cN
    cV
    cU
    cE
    cT
    hdmap10.v
    @28
    hdmap10.n
    @29
    @11
    @12
    lspprcl
    #
    wph
    cN
    cV
    cU
    cE
    cT
    hdmap10.v
    hdmap10.n
    @29
    @11
    @12
    lspprid1
    lspsnel5a
    wph
    @27
    @1
    cN
    cU
    cT
    @28
    hdmap10.n
    @29
    @30
    wph
    cN
    cV
    cU
    cE
    cT
    hdmap10.v
    hdmap10.n
    @29
    @11
    @12
    lspprid2
    lspsnel5a
    unssd
    sseld
    con3dimp
    3adant2
    hdmapval2
    eqcomd
    @14
    cC
    cD
    @18
    cU
    @17
    @5
    cH
    cI
    cK
    cL
    cM
    @15
    cN
    cV
    cW
    @0
    cT
    c.0
    hdmap10.h
    hdmap10.u
    hdmap10.v
    @15
    eqid
    #
    hdmap10.o
    hdmap10.n
    hdmap10.c
    hdmap10.d
    @18
    eqid
    #
    hdmap10.l
    hdmap10.m
    hdmap10.i
    @21
    @14
    @27
    @1
    cV
    cU
    @0
    c.0
    hdmap10.v
    hdmap10.o
    @28
    wph
    @13
    cU
    clmod
    wcel
    @3
    @29
    3ad2ant1
    wph
    @13
    @1
    @27
    wcel
    @3
    @30
    3ad2ant1
    @23
    wph
    @13
    @3
    simp3
    #
    lssneln0
    #
    @14
    cC
    cD
    cU
    @16
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cE
    @0
    c.0
    hdmap10.h
    hdmap10.u
    hdmap10.v
    hdmap10.o
    hdmap10.n
    hdmap10.c
    hdmap10.d
    hdmap10.l
    hdmap10.m
    hdmap10.i
    @21
    wph
    @13
    @16
    cD
    wcel
    @3
    wph
    @16
    cD
    cC
    c0g
    cfv
    #
    csn
    wph
    cC
    cU
    cD
    cH
    cK
    cJ
    @35
    cV
    cW
    cE
    c.0
    hdmap10.h
    hdmap10.u
    hdmap10.v
    hdmap10.o
    hdmap10.c
    hdmap10.d
    @35
    eqid
    hdmap10.j
    hdmap10.k
    @10
    hvmapcl2
    eldifad
    3ad2ant1
    #
    wph
    @13
    @24
    cM
    cfv
    @16
    csn
    cL
    cfv
    wceq
    @3
    wph
    cC
    cJ
    cU
    cH
    cL
    cK
    cM
    cN
    cV
    cW
    cE
    c.0
    hdmap10.h
    hdmap10.u
    hdmap10.v
    hdmap10.o
    hdmap10.n
    hdmap10.c
    hdmap10.l
    hdmap10.m
    hdmap10.j
    hdmap10.k
    @10
    mapdhvmap
    3ad2ant1
    #
    @14
    @0
    csn
    cN
    cfv
    #
    @24
    @14
    @38
    @24
    wne
    #
    @38
    @4
    wne
    #
    @14
    cN
    cV
    cU
    @0
    cE
    cT
    hdmap10.v
    hdmap10.n
    wph
    @13
    cU
    clvec
    wcel
    @3
    wph
    cU
    cH
    cK
    cW
    hdmap10.h
    hdmap10.u
    hdmap10.k
    dvhlvec
    3ad2ant1
    @23
    wph
    @13
    cE
    cV
    wcel
    @3
    @11
    3ad2ant1
    @22
    @33
    lspindpi
    #
    simpld
    necomd
    #
    wph
    @13
    cE
    cV
    @7
    cdif
    #
    wcel
    @3
    @10
    3ad2ant1
    #
    @23
    hdmap1cl
    #
    wph
    @13
    cT
    @43
    wcel
    @3
    hdmap10lem.t
    3ad2ant1
    wph
    @13
    @5
    cD
    wcel
    @3
    wph
    cC
    cD
    cS
    cT
    cU
    cH
    cK
    cV
    cW
    hdmap10.h
    hdmap10.u
    hdmap10.v
    hdmap10.c
    hdmap10.d
    hdmap10.s
    hdmap10.k
    @12
    hdmapcl
    3ad2ant1
    @14
    @39
    @40
    @41
    simprd
    @14
    @38
    cM
    cfv
    @17
    csn
    cL
    cfv
    wceq
    #
    cE
    @0
    @15
    co
    csn
    cN
    cfv
    cM
    cfv
    @16
    @17
    @18
    co
    csn
    cL
    cfv
    wceq
    #
    @14
    @17
    @17
    wceq
    @46
    @47
    wa
    @17
    eqid
    @14
    cC
    cD
    @18
    cU
    @16
    @17
    cH
    cI
    cK
    cL
    cM
    @15
    cN
    cV
    cW
    cE
    @0
    c.0
    hdmap10.h
    hdmap10.u
    hdmap10.v
    @31
    hdmap10.o
    hdmap10.n
    hdmap10.c
    hdmap10.d
    @32
    hdmap10.l
    hdmap10.m
    hdmap10.i
    @21
    @44
    @36
    @34
    @45
    @42
    @37
    hdmap1eq
    mpbii
    simpld
    hdmap1eq
    mpbid
    simpld
    rexlimdv3a
    mpd
end
