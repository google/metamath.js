include "co.mm"
include "csn.mm"
include "cfv.mm"
include "clsm.mm"
include "cin.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmcl.mm"
include "mapdin.mm"
include "mapdlsm.mm"
include "ineq12d.mm"
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
include "simprd.mm"
include "lspindp1.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "baerlem5a.mm"
include "fveq2d.mm"
include "lcdlvec.mm"
include "mapdindp.mm"
include "mapdncol.mm"
include "mapdn0.mm"
include "3eqtr4d.mm"

theorem mapdh6lem1N
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
  assert |- ( ph -> ( M ` ( N ` { ( X .- ( Y .+ Z ) ) } ) ) = ( J ` { ( F R ( G .+b E ) ) } ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
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
    cZ
    c.mi
    co
    #
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    @3
    co
    #
    cin
    #
    cM
    cfv
    #
    cF
    cG
    cR
    co
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
    cE
    cR
    co
    csn
    cJ
    cfv
    #
    cG
    csn
    cJ
    cfv
    #
    @13
    co
    #
    cin
    #
    cX
    cY
    cZ
    c.pl
    co
    c.mi
    co
    csn
    cN
    cfv
    #
    cM
    cfv
    cF
    cG
    cE
    c.pb
    co
    cR
    co
    csn
    cJ
    cfv
    wph
    @10
    @4
    cM
    cfv
    #
    @8
    cM
    cfv
    #
    cin
    #
    @18
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
    @4
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
    @1
    @23
    wcel
    #
    @2
    @23
    wcel
    #
    @4
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
    @0
    cV
    wcel
    #
    @26
    @28
    wph
    @25
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @29
    @28
    wph
    cX
    cV
    c.0
    csn
    #
    mapdhcl.x
    eldifad
    #
    wph
    cY
    cV
    @32
    mapdhe6.y
    eldifad
    #
    c.mi
    cV
    cU
    cX
    cY
    mapdh.v
    mapdh.s
    lmodvsubcl
    syl3anc
    @23
    cN
    cV
    cU
    @0
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
    @32
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
    @3
    @23
    @1
    @2
    cU
    @24
    @3
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
    @40
    @28
    wph
    @25
    @30
    @36
    @42
    @28
    @33
    @37
    c.mi
    cV
    cU
    cX
    cZ
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
    @31
    @41
    @28
    @34
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
    @3
    @23
    @6
    @7
    cU
    @24
    @39
    lsmcl
    syl3anc
    mapdin
    wph
    @22
    @1
    cM
    cfv
    #
    @2
    cM
    cfv
    #
    @13
    co
    #
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
    #
    cin
    @18
    wph
    @20
    @47
    @21
    @50
    wph
    cC
    @13
    @3
    @23
    cU
    cH
    cK
    cM
    cW
    @1
    @2
    mapdh.h
    mapdh.m
    mapdh.u
    @24
    @39
    mapdh.c
    @13
    eqid
    #
    mapdh.k
    @35
    @38
    mapdlsm
    wph
    cC
    @13
    @3
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
    @39
    mapdh.c
    @51
    mapdh.k
    @43
    @44
    mapdlsm
    ineq12d
    wph
    @47
    @14
    @50
    @17
    wph
    @45
    @11
    @46
    @12
    @13
    wph
    @49
    @16
    wceq
    #
    @45
    @11
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
    @52
    @53
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
    @54
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
    @34
    wph
    cX
    csn
    cN
    cfv
    #
    @7
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
    @34
    mapdhe6.z
    @33
    mapdh6.yz
    mapdhe6.xn
    lspindp2
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    @57
    mapdheq
    mpbid
    #
    simprd
    wph
    @46
    @12
    wceq
    #
    @48
    @15
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
    @60
    @61
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
    @62
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
    @37
    wph
    @55
    @2
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
    @56
    mapdhe6.y
    @37
    @33
    mapdh6.yz
    mapdhe6.xn
    lspindp1
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    @63
    mapdheq
    mpbid
    #
    simpld
    #
    oveq12d
    wph
    @48
    @15
    @49
    @16
    @13
    wph
    @60
    @61
    @65
    simprd
    wph
    @52
    @53
    @59
    simpld
    #
    oveq12d
    ineq12d
    eqtrd
    eqtrd
    wph
    @19
    @9
    cM
    wph
    c.pl
    @3
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
    @39
    mapdh.n
    @56
    @33
    mapdhe6.xn
    mapdh6.yz
    mapdhe6.y
    mapdhe6.z
    mapdh.p
    baerlem5a
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
    @51
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
    @33
    @34
    @58
    @67
    @37
    @64
    @66
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
    @58
    @67
    @34
    @37
    @64
    @66
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
    @58
    @67
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
    @64
    @66
    mapdhc.o
    mapdh.q
    mapdhe6.z
    mapdn0
    mapdh.a
    baerlem5a
    3eqtr4d
end
