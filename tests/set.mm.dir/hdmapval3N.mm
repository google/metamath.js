include "cfv.mm"
include "cotp.mm"
include "wceq.mm"
include "c0g.mm"
include "fveq2.mm"
include "oteq3.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "csn.mm"
include "cbs.mm"
include "cltrn.mm"
include "eqid.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "dvh3dim.mm"
include "adantr.mm"
include "w3a.mm"
include "chlt.mm"
include "simp1l.mm"
include "syl.mm"
include "cdif.mm"
include "simp1r.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simp2.mm"
include "simp3.mm"
include "hdmapval3lemN.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "hdmapval0.mm"
include "hvmapcl2.mm"
include "hdmap1val0.mm"
include "eqtr4d.mm"
include "pm2.61ne.mm"

theorem hdmapval3N
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
  let cN: class N
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume hdmapval3.h: |- H = ( LHyp ` K )
  assume hdmapval3.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapval3.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapval3.v: |- V = ( Base ` U )
  assume hdmapval3.n: |- N = ( LSpan ` U )
  assume hdmapval3.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapval3.d: |- D = ( Base ` C )
  assume hdmapval3.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapval3.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmapval3.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapval3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapval3.te: |- ( ph -> ( N ` { T } ) =/= ( N ` { E } ) )
  assume hdmapval3.t: |- ( ph -> T e. V )


  assert |- ( ph -> ( S ` T ) = ( I ` <. E , ( J ` E ) , T >. ) )

  proof
    wph
    cT
    cS
    cfv
    #
    cE
    cE
    cJ
    cfv
    #
    cT
    cotp
    #
    cI
    cfv
    #
    wceq
    #
    cU
    c0g
    cfv
    #
    cS
    cfv
    #
    cE
    @1
    @5
    cotp
    #
    cI
    cfv
    #
    wceq
    cT
    @5
    cT
    @5
    wceq
    #
    @0
    @6
    @3
    @8
    cT
    @5
    cS
    fveq2
    @9
    @2
    @7
    cI
    cT
    @5
    cE
    @1
    oteq3
    fveq2d
    eqeq12d
    wph
    cT
    @5
    wne
    #
    wa
    #
    vx
    cv
    #
    cE
    cT
    cpr
    cN
    cfv
    wcel
    wn
    #
    vx
    cV
    wrex
    #
    @4
    wph
    @14
    @10
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
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    hdmapval3.n
    hdmapval3.k
    wph
    cE
    cV
    @5
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
    @5
    hdmapval3.h
    @16
    eqid
    @17
    eqid
    hdmapval3.u
    hdmapval3.v
    @5
    eqid
    #
    hdmapval3.e
    hdmapval3.k
    dvheveccl
    #
    eldifad
    #
    hdmapval3.t
    dvh3dim
    adantr
    @11
    @13
    @4
    vx
    cV
    @11
    @12
    cV
    wcel
    #
    @13
    w3a
    #
    vx
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
    hdmapval3.h
    hdmapval3.e
    hdmapval3.u
    hdmapval3.v
    hdmapval3.n
    hdmapval3.c
    hdmapval3.d
    hdmapval3.j
    hdmapval3.i
    hdmapval3.s
    @22
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    wph
    @10
    @21
    @13
    simp1l
    #
    hdmapval3.k
    syl
    @22
    wph
    cT
    csn
    cN
    cfv
    cE
    csn
    cN
    cfv
    wne
    @23
    hdmapval3.te
    syl
    @22
    cT
    cV
    wcel
    #
    @10
    cT
    cV
    @15
    cdif
    wcel
    @22
    wph
    @24
    @23
    hdmapval3.t
    syl
    wph
    @10
    @21
    @13
    simp1r
    cT
    cV
    @5
    eldifsn
    sylanbrc
    @11
    @21
    @13
    simp2
    @11
    @21
    @13
    simp3
    hdmapval3lemN
    rexlimdv3a
    mpd
    wph
    @6
    cC
    c0g
    cfv
    #
    @8
    wph
    cC
    @25
    cS
    cU
    cH
    cK
    cW
    @5
    hdmapval3.h
    hdmapval3.u
    @18
    hdmapval3.c
    @25
    eqid
    #
    hdmapval3.s
    hdmapval3.k
    hdmapval0
    wph
    cC
    cD
    @25
    cU
    @1
    cH
    cI
    cK
    cV
    cW
    cE
    @5
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    @18
    hdmapval3.c
    hdmapval3.d
    @26
    hdmapval3.i
    hdmapval3.k
    wph
    @1
    cD
    @25
    csn
    wph
    cC
    cU
    cD
    cH
    cK
    cJ
    @25
    cV
    cW
    cE
    @5
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    @18
    hdmapval3.c
    hdmapval3.d
    @26
    hdmapval3.j
    hdmapval3.k
    @19
    hvmapcl2
    eldifad
    @20
    hdmap1val0
    eqtr4d
    pm2.61ne
end
