include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "wcel.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "csn.mm"
include "eldifad.mm"
include "hdmapcl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "hdmaprnN.mm"
include "eleqtrrd.mm"
include "wfn.mm"
include "wb.mm"
include "hdmapfnN.mm"
include "fvelrnb.mm"
include "syl.mm"
include "mpbid.mm"
include "w3a.mm"
include "clspn.mm"
include "cmpd.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "hgmaprnlem3N.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hgmaprnlem4N
  let wph: wff ph
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  assume hgmaprnlem1.h: |- H = ( LHyp ` K )
  assume hgmaprnlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmaprnlem1.v: |- V = ( Base ` U )
  assume hgmaprnlem1.r: |- R = ( Scalar ` U )
  assume hgmaprnlem1.b: |- B = ( Base ` R )
  assume hgmaprnlem1.t: |- .x. = ( .s ` U )
  assume hgmaprnlem1.o: |- .0. = ( 0g ` U )
  assume hgmaprnlem1.c: |- C = ( ( LCDual ` K ) ` W )
  assume hgmaprnlem1.d: |- D = ( Base ` C )
  assume hgmaprnlem1.p: |- P = ( Scalar ` C )
  assume hgmaprnlem1.a: |- A = ( Base ` P )
  assume hgmaprnlem1.e: |- .xb = ( .s ` C )
  assume hgmaprnlem1.q: |- Q = ( 0g ` C )
  assume hgmaprnlem1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hgmaprnlem1.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmaprnlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmaprnlem1.z: |- ( ph -> z e. A )
  assume hgmaprnlem1.t2: |- ( ph -> t e. ( V \ { .0. } ) )

  disjoint t z
  disjoint .xb s
  disjoint G s
  disjoint S s
  disjoint V s
  disjoint ph s
  disjoint s t
  disjoint s z
  assert |- ( ph -> z e. ran G )

  proof
    wph
    vs
    cv
    #
    cS
    cfv
    vz
    cv
    #
    vt
    cv
    #
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    vs
    cV
    wrex
    #
    @1
    cG
    crn
    wcel
    #
    wph
    @4
    cS
    crn
    #
    wcel
    #
    @6
    wph
    @4
    cD
    @8
    wph
    cC
    clmod
    wcel
    @1
    cA
    wcel
    #
    @3
    cD
    wcel
    @4
    cD
    wcel
    wph
    cC
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.c
    hgmaprnlem1.k
    lcdlmod
    hgmaprnlem1.z
    wph
    cC
    cD
    cS
    @2
    cU
    cH
    cK
    cV
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.c
    hgmaprnlem1.d
    hgmaprnlem1.s
    hgmaprnlem1.k
    wph
    @2
    cV
    c.0
    csn
    #
    hgmaprnlem1.t2
    eldifad
    hdmapcl
    @1
    c.xb
    cP
    cA
    cD
    cC
    @3
    hgmaprnlem1.d
    hgmaprnlem1.p
    hgmaprnlem1.e
    hgmaprnlem1.a
    lmodvscl
    syl3anc
    wph
    cC
    cD
    cS
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.c
    hgmaprnlem1.d
    hgmaprnlem1.s
    hgmaprnlem1.k
    hdmaprnN
    eleqtrrd
    wph
    cS
    cV
    wfn
    @9
    @6
    wb
    wph
    cS
    cU
    cH
    cK
    cV
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.s
    hgmaprnlem1.k
    hdmapfnN
    vs
    cV
    @4
    cS
    fvelrnb
    syl
    mpbid
    wph
    @5
    @7
    vs
    cV
    wph
    @0
    cV
    wcel
    #
    @5
    w3a
    vz
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    c.xb
    c.x
    cU
    cG
    cH
    cK
    cC
    clspn
    cfv
    #
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cU
    clspn
    cfv
    #
    cV
    cW
    c.0
    vs
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.t
    hgmaprnlem1.o
    hgmaprnlem1.c
    hgmaprnlem1.d
    hgmaprnlem1.p
    hgmaprnlem1.a
    hgmaprnlem1.e
    hgmaprnlem1.q
    hgmaprnlem1.s
    hgmaprnlem1.g
    wph
    @12
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @5
    hgmaprnlem1.k
    3ad2ant1
    wph
    @12
    @10
    @5
    hgmaprnlem1.z
    3ad2ant1
    wph
    @12
    @2
    cV
    @11
    cdif
    wcel
    @5
    hgmaprnlem1.t2
    3ad2ant1
    wph
    @12
    @5
    simp2
    wph
    @12
    @5
    simp3
    @14
    eqid
    @15
    eqid
    @13
    eqid
    hgmaprnlem3N
    rexlimdv3a
    mpd
end
