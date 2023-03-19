include "csn.mm"
include "cfv.mm"
include "clsm.mm"
include "co.mm"
include "cin.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lmodvacl.mm"
include "lmodvsubcl.mm"
include "mapdin.mm"
include "mapdlsm.mm"
include "wceq.mm"
include "cotp.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "wn.mm"
include "dvhlvec.mm"
include "lspindp2.mm"
include "simpld.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "lspindp1.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "mapdh6lem1N.mm"
include "ineq12d.mm"
include "baerlem5b.mm"
include "fveq2d.mm"
include "lcdlvec.mm"
include "mapdindp.mm"
include "mapdncol.mm"
include "mapdn0.mm"
include "3eqtr4d.mm"

theorem mapdh6lem2N
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
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
  let vw: setvar w
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
  assume mapdhe6.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdhe6.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdhe6.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh6.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume mapdh6.fg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh6.fe: |- ( ph -> ( I ` <. X , F , Z >. ) = E )

  disjoint E h
  disjoint h x
  disjoint Z h
  disjoint Z x
  disjoint .+b h
  disjoint I h
  disjoint .+ h
  disjoint .+ x
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
  disjoint G h
  disjoint G x
  disjoint E h
  disjoint Z h
  disjoint Z x
  disjoint h w
  assert |- ( ph -> ( M ` ( N ` { ( Y .+ Z ) } ) ) = ( J ` { ( G .+b E ) } ) )

  proof
    wph
    cY
    csn
    cN
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    cU
    clsm
    cfv
    #
    co
    #
    cX
    cY
    cZ
    c.pl
    co
    #
    c.mi
    co
    #
    csn
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    @2
    co
    #
    cin
    #
    cM
    cfv
    #
    cG
    csn
    cJ
    cfv
    #
    cE
    csn
    cJ
    cfv
    #
    cC
    clsm
    cfv
    #
    co
    #
    cF
    cG
    cE
    c.pb
    co
    #
    cR
    co
    csn
    cJ
    cfv
    #
    cF
    csn
    cJ
    cfv
    #
    @13
    co
    #
    cin
    #
    @4
    csn
    cN
    cfv
    #
    cM
    cfv
    @15
    csn
    cJ
    cfv
    wph
    @10
    @3
    cM
    cfv
    #
    @8
    cM
    cfv
    #
    cin
    @19
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
    @3
    @8
    mapdh.h
    mapdh.m
    mapdh.u
    @23
    eqid
    #
    mapdh.k
    wph
    cU
    clmod
    wcel
    #
    @0
    @23
    wcel
    #
    @1
    @23
    wcel
    #
    @3
    @23
    wcel
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
    wph
    @25
    cY
    cV
    wcel
    #
    @26
    @28
    wph
    cY
    cV
    c.0
    csn
    #
    mapdhe6.y
    eldifad
    #
    @23
    cN
    cV
    cU
    cY
    mapdh.v
    @24
    mapdh.n
    lspsncl
    syl2anc
    #
    wph
    @25
    cZ
    cV
    wcel
    #
    @27
    @28
    wph
    cZ
    cV
    @30
    mapdhe6.z
    eldifad
    #
    @23
    cN
    cV
    cU
    cZ
    mapdh.v
    @24
    mapdh.n
    lspsncl
    syl2anc
    #
    @2
    @23
    @0
    @1
    cU
    @24
    @2
    eqid
    #
    lsmcl
    syl3anc
    wph
    @25
    @6
    @23
    wcel
    #
    @7
    @23
    wcel
    #
    @8
    @23
    wcel
    @28
    wph
    @25
    @5
    cV
    wcel
    #
    @37
    @28
    wph
    @25
    cX
    cV
    wcel
    #
    @4
    cV
    wcel
    #
    @39
    @28
    wph
    cX
    cV
    @30
    mapdhcl.x
    eldifad
    #
    wph
    @25
    @29
    @33
    @41
    @28
    @31
    @34
    c.pl
    cV
    cU
    cY
    cZ
    mapdh.v
    mapdh.p
    lmodvacl
    syl3anc
    c.mi
    cV
    cU
    cX
    @4
    mapdh.v
    mapdh.s
    lmodvsubcl
    syl3anc
    @23
    cN
    cV
    cU
    @5
    mapdh.v
    @24
    mapdh.n
    lspsncl
    syl2anc
    #
    wph
    @25
    @40
    @38
    @28
    @42
    @23
    cN
    cV
    cU
    cX
    mapdh.v
    @24
    mapdh.n
    lspsncl
    syl2anc
    #
    @2
    @23
    @6
    @7
    cU
    @24
    @36
    lsmcl
    syl3anc
    mapdin
    wph
    @21
    @14
    @22
    @18
    wph
    @21
    @0
    cM
    cfv
    #
    @1
    cM
    cfv
    #
    @13
    co
    @14
    wph
    cC
    @13
    @2
    @23
    cU
    cH
    cK
    cM
    cW
    @0
    @1
    mapdh.h
    mapdh.m
    mapdh.u
    @24
    @36
    mapdh.c
    @13
    eqid
    #
    mapdh.k
    @32
    @35
    mapdlsm
    wph
    @45
    @11
    @46
    @12
    @13
    wph
    @45
    @11
    wceq
    #
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    cG
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cG
    wceq
    @48
    @49
    wa
    mapdh6.fg
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cG
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
    cY
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
    mapdhe6.y
    wph
    @50
    cG
    cD
    mapdh6.fg
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
    cY
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
    @31
    wph
    @7
    @0
    wne
    cZ
    cX
    cY
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cU
    cY
    cZ
    c.0
    cX
    mapdh.v
    mapdhc.o
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
    @31
    mapdhe6.z
    @42
    mapdh6.yz
    mapdhe6.xn
    lspindp2
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    @52
    mapdheq
    mpbid
    simpld
    #
    wph
    @46
    @12
    wceq
    #
    cX
    cZ
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    cE
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    cX
    cF
    cZ
    cotp
    cI
    cfv
    #
    cE
    wceq
    @55
    @56
    wa
    mapdh6.fe
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cE
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
    cZ
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
    mapdhe6.z
    wph
    @57
    cE
    cD
    mapdh6.fe
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
    cZ
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
    @34
    wph
    @7
    @1
    wne
    cY
    cX
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cU
    cY
    cZ
    c.0
    cX
    mapdh.v
    mapdhc.o
    mapdh.n
    @51
    mapdhe6.y
    @34
    @42
    mapdh6.yz
    mapdhe6.xn
    lspindp1
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    @58
    mapdheq
    mpbid
    simpld
    #
    oveq12d
    eqtrd
    wph
    @22
    @6
    cM
    cfv
    #
    @7
    cM
    cfv
    #
    @13
    co
    @18
    wph
    cC
    @13
    @2
    @23
    cU
    cH
    cK
    cM
    cW
    @6
    @7
    mapdh.h
    mapdh.m
    mapdh.u
    @24
    @36
    mapdh.c
    @47
    mapdh.k
    @43
    @44
    mapdlsm
    wph
    @61
    @16
    @62
    @17
    @13
    wph
    vx
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    vh
    cE
    cF
    cG
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
    cY
    c.0
    cZ
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
    mapdh.p
    mapdh.a
    mapdhe6.y
    mapdhe6.z
    mapdhe6.xn
    mapdh6.yz
    mapdh6.fg
    mapdh6.fe
    mapdh6lem1N
    mapdh.mn
    oveq12d
    eqtrd
    ineq12d
    eqtrd
    wph
    @20
    @9
    cM
    wph
    c.pl
    @2
    c.mi
    cN
    cV
    cU
    cX
    cY
    c.0
    cZ
    mapdh.v
    mapdh.s
    mapdhc.o
    @36
    mapdh.n
    @51
    @42
    mapdhe6.xn
    mapdh6.yz
    mapdhe6.y
    mapdhe6.z
    mapdh.p
    baerlem5b
    fveq2d
    wph
    c.pb
    @13
    cR
    cJ
    cD
    cC
    cF
    cG
    cQ
    cE
    mapdh.d
    mapdh.r
    mapdh.q
    @47
    mapdh.j
    wph
    cC
    cH
    cK
    cW
    mapdh.h
    mapdh.c
    mapdh.k
    lcdlvec
    mapdhc.f
    wph
    cC
    cD
    cU
    cE
    cF
    cG
    cH
    cJ
    cK
    cM
    cN
    cV
    cW
    cX
    cY
    cZ
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    @42
    @31
    @53
    @54
    @34
    @59
    @60
    mapdhe6.xn
    mapdindp
    wph
    cC
    cD
    cU
    cG
    cE
    cH
    cJ
    cK
    cM
    cN
    cV
    cW
    cY
    cZ
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.j
    mapdh.k
    @53
    @54
    @31
    @34
    @59
    @60
    mapdh6.yz
    mapdncol
    wph
    cC
    cD
    cU
    cG
    cH
    cJ
    cK
    cM
    cN
    cV
    cW
    cY
    c.0
    cQ
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.j
    mapdh.k
    @53
    @54
    mapdhc.o
    mapdh.q
    mapdhe6.y
    mapdn0
    wph
    cC
    cD
    cU
    cE
    cH
    cJ
    cK
    cM
    cN
    cV
    cW
    cZ
    c.0
    cQ
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.j
    mapdh.k
    @59
    @60
    mapdhc.o
    mapdh.q
    mapdhe6.z
    mapdn0
    mapdh.a
    baerlem5b
    3eqtr4d
end
