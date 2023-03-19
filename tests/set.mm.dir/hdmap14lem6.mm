include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wreu.mm"
include "c0g.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "lmod0cl.mm"
include "syl.mm"
include "cbs.mm"
include "eqid.mm"
include "csn.mm"
include "eldifad.mm"
include "hdmapcl.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "w3a.mm"
include "wn.mm"
include "cdif.mm"
include "wne.mm"
include "hdmapnzcl.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "3ad2ant1.mm"
include "wo.mm"
include "simp3l.mm"
include "clvec.mm"
include "lcdlvec.mm"
include "simp2l.mm"
include "lvecvs0or.mm"
include "mpbid.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "simp3r.mm"
include "simp2r.mm"
include "eqtr4d.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "reu4.mm"
include "sylanbrc.mm"
include "oveq1d.mm"
include "dvhlmod.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "hdmapval0.mm"
include "eqeq1d.mm"
include "reubidv.mm"
include "mpbird.mm"

theorem hdmap14lem6
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vh: setvar h
  assume hdmap14lem1.h: |- H = ( LHyp ` K )
  assume hdmap14lem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem1.v: |- V = ( Base ` U )
  assume hdmap14lem1.t: |- .x. = ( .s ` U )
  assume hdmap14lem3.o: |- .0. = ( 0g ` U )
  assume hdmap14lem1.r: |- R = ( Scalar ` U )
  assume hdmap14lem1.b: |- B = ( Base ` R )
  assume hdmap14lem1.z: |- Z = ( 0g ` R )
  assume hdmap14lem1.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem2.e: |- .xb = ( .s ` C )
  assume hdmap14lem1.l: |- L = ( LSpan ` C )
  assume hdmap14lem2.p: |- P = ( Scalar ` C )
  assume hdmap14lem2.a: |- A = ( Base ` P )
  assume hdmap14lem2.q: |- Q = ( 0g ` P )
  assume hdmap14lem1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem3.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap14lem6.f: |- ( ph -> F = Z )

  disjoint A g
  disjoint C g
  disjoint .xb g
  disjoint Q g
  disjoint S g
  disjoint X g
  disjoint g ph
  disjoint g h
  disjoint A h
  disjoint C h
  disjoint .xb h
  disjoint S h
  disjoint X h
  disjoint h ph
  assert |- ( ph -> E! g e. A ( S ` ( F .x. X ) ) = ( g .xb ( S ` X ) ) )

  proof
    wph
    cF
    cX
    c.x
    co
    #
    cS
    cfv
    #
    vg
    cv
    #
    cX
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    vg
    cA
    wreu
    cC
    c0g
    cfv
    #
    @4
    wceq
    #
    vg
    cA
    wreu
    #
    wph
    @7
    vg
    cA
    wrex
    #
    @7
    @6
    vh
    cv
    #
    @3
    c.xb
    co
    #
    wceq
    #
    wa
    #
    vg
    vh
    weq
    #
    wi
    #
    vh
    cA
    wral
    vg
    cA
    wral
    @8
    wph
    cQ
    cA
    wcel
    #
    @6
    cQ
    @3
    c.xb
    co
    #
    wceq
    #
    @9
    wph
    cC
    clmod
    wcel
    #
    @16
    wph
    cC
    cH
    cK
    cW
    hdmap14lem1.h
    hdmap14lem1.c
    hdmap14lem1.k
    lcdlmod
    #
    cP
    cA
    cC
    cQ
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem2.q
    lmod0cl
    syl
    wph
    @17
    @6
    wph
    @19
    @3
    cC
    cbs
    cfv
    #
    wcel
    #
    @17
    @6
    wceq
    @20
    wph
    cC
    @21
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem1.c
    @21
    eqid
    #
    hdmap14lem1.s
    hdmap14lem1.k
    wph
    cX
    cV
    c.0
    csn
    hdmap14lem3.x
    eldifad
    #
    hdmapcl
    #
    c.xb
    cP
    cQ
    @21
    cC
    @3
    @6
    @23
    hdmap14lem2.p
    hdmap14lem2.e
    hdmap14lem2.q
    @6
    eqid
    #
    lmod0vs
    syl2anc
    eqcomd
    @7
    @18
    vg
    cQ
    cA
    @2
    cQ
    wceq
    #
    @4
    @17
    @6
    @2
    cQ
    @3
    c.xb
    oveq1
    eqeq2d
    rspcev
    syl2anc
    wph
    @15
    vg
    vh
    cA
    cA
    wph
    @2
    cA
    wcel
    #
    @10
    cA
    wcel
    #
    wa
    #
    @13
    @14
    wph
    @30
    @13
    w3a
    #
    @2
    cQ
    @10
    @31
    @3
    @6
    wceq
    #
    wn
    #
    @27
    wph
    @30
    @33
    @13
    wph
    @3
    @6
    wph
    @3
    @21
    @6
    csn
    cdif
    wcel
    @3
    @6
    wne
    wph
    cC
    @21
    @6
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    c.0
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem3.o
    hdmap14lem1.c
    @26
    @23
    hdmap14lem1.s
    hdmap14lem1.k
    hdmap14lem3.x
    hdmapnzcl
    @3
    @21
    @6
    eldifsni
    syl
    neneqd
    3ad2ant1
    #
    @31
    @32
    @27
    @31
    @27
    @32
    @31
    @4
    @6
    wceq
    @27
    @32
    wo
    @31
    @6
    @4
    wph
    @30
    @7
    @12
    simp3l
    eqcomd
    @31
    @2
    c.xb
    cP
    cA
    cQ
    @21
    cC
    @3
    @6
    @23
    hdmap14lem2.e
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem2.q
    @26
    wph
    @30
    cC
    clvec
    wcel
    @13
    wph
    cC
    cH
    cK
    cW
    hdmap14lem1.h
    hdmap14lem1.c
    hdmap14lem1.k
    lcdlvec
    3ad2ant1
    #
    wph
    @28
    @29
    @13
    simp2l
    wph
    @30
    @22
    @13
    @25
    3ad2ant1
    #
    lvecvs0or
    mpbid
    orcomd
    ord
    mpd
    @31
    @33
    @10
    cQ
    wceq
    #
    @34
    @31
    @32
    @37
    @31
    @37
    @32
    @31
    @11
    @6
    wceq
    @37
    @32
    wo
    @31
    @6
    @11
    wph
    @30
    @7
    @12
    simp3r
    eqcomd
    @31
    @10
    c.xb
    cP
    cA
    cQ
    @21
    cC
    @3
    @6
    @23
    hdmap14lem2.e
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem2.q
    @26
    @35
    wph
    @28
    @29
    @13
    simp2r
    @36
    lvecvs0or
    mpbid
    orcomd
    ord
    mpd
    eqtr4d
    3exp
    ralrimivv
    @7
    @12
    vg
    vh
    cA
    @14
    @4
    @11
    @6
    @2
    @10
    @3
    c.xb
    oveq1
    eqeq2d
    reu4
    sylanbrc
    wph
    @5
    @7
    vg
    cA
    wph
    @1
    @6
    @4
    wph
    @1
    c.0
    cS
    cfv
    @6
    wph
    @0
    c.0
    cS
    wph
    @0
    cZ
    cX
    c.x
    co
    #
    c.0
    wph
    cF
    cZ
    cX
    c.x
    hdmap14lem6.f
    oveq1d
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    @38
    c.0
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.k
    dvhlmod
    @24
    c.x
    cR
    cZ
    cV
    cU
    cX
    c.0
    hdmap14lem1.v
    hdmap14lem1.r
    hdmap14lem1.t
    hdmap14lem1.z
    hdmap14lem3.o
    lmod0vs
    syl2anc
    eqtrd
    fveq2d
    wph
    cC
    @6
    cS
    cU
    cH
    cK
    cW
    c.0
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem3.o
    hdmap14lem1.c
    @26
    hdmap14lem1.s
    hdmap14lem1.k
    hdmapval0
    eqtrd
    eqeq1d
    reubidv
    mpbird
end
