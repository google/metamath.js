include "cv.mm"
include "co.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "clmod.mm"
include "wcel.mm"
include "lcdlmod.mm"
include "csn.mm"
include "eldifad.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "mapdhcl.mm"
include "lmod0vrid.mm"
include "syl2anc.mm"
include "adantr.mm"
include "oteq3.mm"
include "fveq2d.mm"
include "cdif.mm"
include "mapdhval0.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "dvhlmod.mm"
include "oteq3d.mm"
include "3eqtr4rd.mm"
include "chlt.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "cpr.mm"
include "wn.mm"
include "mapdindp1.mm"
include "mapdindp2.mm"
include "lspindp1.mm"
include "simprd.mm"
include "lspsnne1.mm"
include "clsm.mm"
include "eqid.mm"
include "lsmpr.mm"
include "csubg.mm"
include "clss.mm"
include "lspsncl.mm"
include "lsssubg.mm"
include "lsmidm.mm"
include "syl.mm"
include "3eqtr2d.mm"
include "neleqtrrd.mm"
include "lspindp4.mm"
include "eqidd.mm"
include "mapdh6aN.mm"
include "pm2.61dane.mm"

theorem mapdh6dN
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let cG: class G
  let cE: class E
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh.h: |- H = ( LHyp ` K )
  assume mapdh.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh.v: |- V = ( Base ` U )
  assume mapdh.s: |- .- = ( -g ` U )
  assume mapdhc.o: |- .0. = ( 0g ` U )
  assume mapdh.n: |- N = ( LSpan ` U )
  assume mapdh.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh.d: |- D = ( Base ` C )
  assume mapdh.r: |- R = ( -g ` C )
  assume mapdh.j: |- J = ( LSpan ` C )
  assume mapdh.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdhc.f: |- ( ph -> F e. D )
  assume mapdh.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdhcl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh.p: |- .+ = ( +g ` U )
  assume mapdh.a: |- .+b = ( +g ` C )
  assume mapdh6d.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh6d.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume mapdh6d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh6d.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh6d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh6d.wn: |- ( ph -> -. w e. ( N ` { X , Y } ) )

  disjoint D x
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J x
  disjoint M x
  disjoint N x
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h ph
  disjoint .0. h
  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint U h
  disjoint .- h
  disjoint h w
  disjoint Z h
  disjoint Z x
  disjoint .+b h
  disjoint I h
  disjoint I x
  disjoint .+ h
  disjoint .+ x
  disjoint w x
  disjoint G h
  disjoint G x
  disjoint E h
  assert |- ( ph -> ( I ` <. X , F , ( w .+ ( Y .+ Z ) ) >. ) = ( ( I ` <. X , F , w >. ) .+b ( I ` <. X , F , ( Y .+ Z ) >. ) ) )

  proof
    wph
    cX
    cF
    vw
    cv
    #
    cY
    cZ
    c.pl
    co
    #
    c.pl
    co
    #
    cotp
    #
    cI
    cfv
    #
    cX
    cF
    @0
    cotp
    #
    cI
    cfv
    #
    cX
    cF
    @1
    cotp
    #
    cI
    cfv
    #
    c.pb
    co
    #
    wceq
    @1
    c.0
    wph
    @1
    c.0
    wceq
    #
    wa
    #
    @6
    cQ
    c.pb
    co
    #
    @6
    @9
    @4
    wph
    @12
    @6
    wceq
    #
    @10
    wph
    cC
    clmod
    wcel
    @6
    cD
    wcel
    @13
    wph
    cC
    cH
    cK
    cW
    mapdh.h
    mapdh.c
    mapdh.k
    lcdlmod
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    @0
    c.0
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    wph
    @0
    cV
    c.0
    csn
    #
    mapdh6d.w
    eldifad
    #
    wph
    @0
    csn
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    wph
    @16
    @17
    wne
    #
    @16
    cY
    csn
    cN
    cfv
    #
    wne
    #
    wph
    cN
    cV
    cU
    @0
    cX
    cY
    mapdh.v
    mapdh.n
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlvec
    #
    @15
    wph
    cX
    cV
    @14
    mapdhcl.x
    eldifad
    #
    wph
    cY
    cV
    @14
    mapdh6d.y
    eldifad
    #
    mapdh6d.wn
    lspindpi
    #
    simpld
    necomd
    mapdhcl
    c.pb
    cD
    cC
    @6
    cQ
    mapdh.d
    mapdh.a
    mapdh.q
    lmod0vrid
    syl2anc
    adantr
    @11
    @8
    cQ
    @6
    c.pb
    @10
    wph
    @8
    cX
    cF
    c.0
    cotp
    #
    cI
    cfv
    cQ
    @10
    @7
    @25
    cI
    @1
    c.0
    cX
    cF
    oteq3
    fveq2d
    wph
    vx
    cV
    @14
    cdif
    #
    cD
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cI
    cJ
    cM
    c.mi
    cN
    cX
    c.0
    mapdh.q
    mapdh.i
    mapdhc.o
    mapdhcl.x
    mapdhc.f
    mapdhval0
    sylan9eqr
    oveq2d
    @11
    @3
    @5
    cI
    @11
    @2
    @0
    cX
    cF
    @10
    wph
    @2
    @0
    c.0
    c.pl
    co
    #
    @0
    @1
    c.0
    @0
    c.pl
    oveq2
    wph
    cU
    clmod
    wcel
    #
    @0
    cV
    wcel
    @27
    @0
    wceq
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlmod
    #
    @15
    c.pl
    cV
    cU
    @0
    c.0
    mapdh.v
    mapdh.p
    mapdhc.o
    lmod0vrid
    syl2anc
    sylan9eqr
    oteq3d
    fveq2d
    3eqtr4rd
    wph
    @1
    c.0
    wne
    #
    wa
    #
    vx
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    vh
    @8
    cF
    @6
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    @0
    c.0
    @1
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @30
    mapdh.k
    adantr
    wph
    cF
    cD
    wcel
    @30
    mapdhc.f
    adantr
    wph
    @17
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    @30
    mapdh.mn
    adantr
    wph
    cX
    @26
    wcel
    @30
    mapdhcl.x
    adantr
    mapdh.p
    mapdh.a
    wph
    @0
    @26
    wcel
    @30
    mapdh6d.w
    adantr
    @31
    @1
    cV
    wcel
    #
    @30
    wa
    @1
    @26
    wcel
    wph
    @32
    @30
    wph
    @28
    cY
    cV
    wcel
    #
    cZ
    cV
    wcel
    @32
    @29
    @23
    wph
    cZ
    cV
    @14
    mapdh6d.z
    eldifad
    #
    c.pl
    cV
    cU
    cY
    cZ
    mapdh.v
    mapdh.p
    lmodvacl
    syl3anc
    #
    anim1i
    @1
    cV
    c.0
    eldifsn
    sylibr
    wph
    cX
    @0
    @1
    cpr
    cN
    cfv
    wcel
    wn
    #
    @30
    wph
    @16
    @1
    csn
    cN
    cfv
    wne
    #
    @36
    wph
    cN
    cV
    cU
    cX
    @1
    c.0
    @0
    mapdh.v
    mapdhc.o
    mapdh.n
    @21
    mapdhcl.x
    @35
    @15
    wph
    vw
    c.pl
    cN
    cV
    cU
    cX
    cY
    c.0
    cZ
    mapdh.v
    mapdh.p
    mapdhc.o
    mapdh.n
    @21
    mapdhcl.x
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.yz
    wph
    @17
    @19
    wne
    @17
    cZ
    csn
    cN
    cfv
    #
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    cZ
    mapdh.v
    mapdh.n
    @21
    @22
    @23
    @34
    mapdh6d.xn
    lspindpi
    simpld
    #
    mapdh6d.wn
    mapdindp1
    wph
    vw
    c.pl
    cN
    cV
    cU
    cX
    cY
    c.0
    cZ
    mapdh.v
    mapdh.p
    mapdhc.o
    mapdh.n
    @21
    mapdhcl.x
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.yz
    @39
    mapdh6d.wn
    mapdindp2
    lspindp1
    simprd
    adantr
    wph
    @37
    @30
    wph
    @20
    @37
    wph
    cN
    cV
    cU
    @0
    cY
    @1
    mapdh.v
    mapdh.n
    @21
    @15
    @23
    @35
    wph
    c.pl
    cN
    cV
    cU
    cY
    cZ
    @0
    mapdh.v
    mapdh.p
    mapdh.n
    @29
    @23
    @34
    @15
    wph
    cY
    cZ
    cpr
    cN
    cfv
    #
    @19
    @0
    wph
    cN
    cV
    cU
    @0
    cY
    c.0
    mapdh.v
    mapdhc.o
    mapdh.n
    @21
    mapdh6d.w
    @23
    wph
    @18
    @20
    @24
    simprd
    lspsnne1
    wph
    @40
    @19
    @38
    cU
    clsm
    cfv
    #
    co
    @19
    @19
    @41
    co
    #
    @19
    wph
    @41
    cN
    cV
    cU
    cY
    cZ
    mapdh.v
    mapdh.n
    @41
    eqid
    #
    @29
    @23
    @34
    lsmpr
    wph
    @19
    @38
    @19
    @41
    mapdh6d.yz
    oveq2d
    wph
    @19
    cU
    csubg
    cfv
    wcel
    #
    @42
    @19
    wceq
    wph
    @28
    @19
    cU
    clss
    cfv
    #
    wcel
    #
    @44
    @29
    wph
    @28
    @33
    @46
    @29
    @23
    @45
    cN
    cV
    cU
    cY
    mapdh.v
    @45
    eqid
    #
    mapdh.n
    lspsncl
    syl2anc
    @45
    @19
    cU
    @47
    lsssubg
    syl2anc
    @41
    @19
    cU
    @43
    lsmidm
    syl
    3eqtr2d
    neleqtrrd
    lspindp4
    lspindpi
    simprd
    adantr
    @31
    @6
    eqidd
    @31
    @8
    eqidd
    mapdh6aN
    pm2.61dane
end
