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
include "wne.mm"
include "dvhlvec.mm"
include "eldifad.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "hdmap1cl.mm"
include "lmod0vrid.mm"
include "syl2anc.mm"
include "adantr.mm"
include "oteq3.mm"
include "fveq2d.mm"
include "hdmap1val0.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "dvhlmod.mm"
include "oteq3d.mm"
include "3eqtr4rd.mm"
include "chlt.mm"
include "cdif.mm"
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
include "hdmap1l6a.mm"
include "pm2.61dane.mm"

theorem hdmap1l6d
  let wph: wff ph
  let vw: setvar w
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume hdmap1l6.h: |- H = ( LHyp ` K )
  assume hdmap1l6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1l6.v: |- V = ( Base ` U )
  assume hdmap1l6.p: |- .+ = ( +g ` U )
  assume hdmap1l6.s: |- .- = ( -g ` U )
  assume hdmap1l6c.o: |- .0. = ( 0g ` U )
  assume hdmap1l6.n: |- N = ( LSpan ` U )
  assume hdmap1l6.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1l6.d: |- D = ( Base ` C )
  assume hdmap1l6.a: |- .+b = ( +g ` C )
  assume hdmap1l6.r: |- R = ( -g ` C )
  assume hdmap1l6.q: |- Q = ( 0g ` C )
  assume hdmap1l6.l: |- L = ( LSpan ` C )
  assume hdmap1l6.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1l6.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1l6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1l6.f: |- ( ph -> F e. D )
  assume hdmap1l6cl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1l6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1l6d.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1l6d.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume hdmap1l6d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1l6d.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume hdmap1l6d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume hdmap1l6d.wn: |- ( ph -> -. w e. ( N ` { X , Y } ) )


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
    hdmap1l6.h
    hdmap1l6.c
    hdmap1l6.k
    lcdlmod
    wph
    cC
    cD
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    @0
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6.mn
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
    @14
    @15
    wne
    #
    @14
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
    hdmap1l6.v
    hdmap1l6.n
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlvec
    #
    wph
    @0
    cV
    c.0
    csn
    #
    hdmap1l6d.w
    eldifad
    #
    wph
    cX
    cV
    @20
    hdmap1l6cl.x
    eldifad
    #
    wph
    cY
    cV
    @20
    hdmap1l6d.y
    eldifad
    #
    hdmap1l6d.wn
    lspindpi
    #
    simpld
    necomd
    hdmap1l6cl.x
    @21
    hdmap1cl
    c.pb
    cD
    cC
    @6
    cQ
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.q
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
    cC
    cD
    cQ
    cU
    cF
    cH
    cI
    cK
    cV
    cW
    cX
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.q
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    @22
    hdmap1val0
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
    @26
    @0
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlmod
    #
    @21
    c.pl
    cV
    cU
    @0
    c.0
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
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
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    @8
    cF
    @6
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    @0
    c.0
    @1
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @29
    hdmap1l6.k
    adantr
    wph
    cF
    cD
    wcel
    @29
    hdmap1l6.f
    adantr
    wph
    cX
    cV
    @20
    cdif
    #
    wcel
    @29
    hdmap1l6cl.x
    adantr
    wph
    @15
    cM
    cfv
    cF
    csn
    cL
    cfv
    wceq
    @29
    hdmap1l6.mn
    adantr
    wph
    @0
    @31
    wcel
    @29
    hdmap1l6d.w
    adantr
    @30
    @1
    cV
    wcel
    #
    @29
    wa
    @1
    @31
    wcel
    wph
    @32
    @29
    wph
    @27
    cY
    cV
    wcel
    #
    cZ
    cV
    wcel
    @32
    @28
    @23
    wph
    cZ
    cV
    @20
    hdmap1l6d.z
    eldifad
    #
    c.pl
    cV
    cU
    cY
    cZ
    hdmap1l6.v
    hdmap1l6.p
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
    @29
    wph
    @14
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
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    @19
    hdmap1l6cl.x
    @35
    @21
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
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    hdmap1l6.n
    @19
    hdmap1l6cl.x
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.yz
    wph
    @15
    @17
    wne
    @15
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
    hdmap1l6.v
    hdmap1l6.n
    @19
    @22
    @23
    @34
    hdmap1l6d.xn
    lspindpi
    simpld
    #
    hdmap1l6d.wn
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
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    hdmap1l6.n
    @19
    hdmap1l6cl.x
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.yz
    @39
    hdmap1l6d.wn
    mapdindp2
    lspindp1
    simprd
    adantr
    wph
    @37
    @29
    wph
    @18
    @37
    wph
    cN
    cV
    cU
    @0
    cY
    @1
    hdmap1l6.v
    hdmap1l6.n
    @19
    @21
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
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.n
    @28
    @23
    @34
    @21
    wph
    cY
    cZ
    cpr
    cN
    cfv
    #
    @17
    @0
    wph
    cN
    cV
    cU
    @0
    cY
    c.0
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    @19
    hdmap1l6d.w
    @23
    wph
    @16
    @18
    @24
    simprd
    lspsnne1
    wph
    @40
    @17
    @38
    cU
    clsm
    cfv
    #
    co
    @17
    @17
    @41
    co
    #
    @17
    wph
    @41
    cN
    cV
    cU
    cY
    cZ
    hdmap1l6.v
    hdmap1l6.n
    @41
    eqid
    #
    @28
    @23
    @34
    lsmpr
    wph
    @17
    @38
    @17
    @41
    hdmap1l6d.yz
    oveq2d
    wph
    @17
    cU
    csubg
    cfv
    wcel
    #
    @42
    @17
    wceq
    wph
    @27
    @17
    cU
    clss
    cfv
    #
    wcel
    #
    @44
    @28
    wph
    @27
    @33
    @46
    @28
    @23
    @45
    cN
    cV
    cU
    cY
    hdmap1l6.v
    @45
    eqid
    #
    hdmap1l6.n
    lspsncl
    syl2anc
    @45
    @17
    cU
    @47
    lsssubg
    syl2anc
    @41
    @17
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
    @30
    @6
    eqidd
    @30
    @8
    eqidd
    hdmap1l6a
    pm2.61dane
end
