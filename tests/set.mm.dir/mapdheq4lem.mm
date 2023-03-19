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
include "simprd.mm"
include "ineq12d.mm"
include "baerlem3.mm"
include "fveq2d.mm"
include "c0g.mm"
include "lcdlvec.mm"
include "mapdindp.mm"
include "mapdncol.mm"
include "mapdn0.mm"
include "3eqtr4d.mm"

theorem mapdheq4lem
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
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
  assume mapdhe4.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdhe.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume mapdh.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh.ee: |- ( ph -> ( I ` <. X , F , Z >. ) = E )

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
  assert |- ( ph -> ( M ` ( N ` { ( Y .- Z ) } ) ) = ( J ` { ( G R E ) } ) )

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
    c.mi
    co
    #
    csn
    cN
    cfv
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
    cR
    co
    csn
    cJ
    cfv
    #
    cF
    cE
    cR
    co
    csn
    cJ
    cfv
    #
    @13
    co
    #
    cin
    #
    cY
    cZ
    c.mi
    co
    csn
    cN
    cfv
    #
    cM
    cfv
    cG
    cE
    cR
    co
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
    @3
    @8
    mapdh.h
    mapdh.m
    mapdh.u
    @22
    eqid
    #
    mapdh.k
    wph
    cU
    clmod
    wcel
    #
    @0
    @22
    wcel
    #
    @1
    @22
    wcel
    #
    @3
    @22
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
    @24
    cY
    cV
    wcel
    #
    @25
    @27
    wph
    cY
    cV
    c.0
    csn
    #
    mapdhe4.y
    eldifad
    #
    @22
    cN
    cV
    cU
    cY
    mapdh.v
    @23
    mapdh.n
    lspsncl
    syl2anc
    #
    wph
    @24
    cZ
    cV
    wcel
    #
    @26
    @27
    wph
    cZ
    cV
    @29
    mapdhe.z
    eldifad
    #
    @22
    cN
    cV
    cU
    cZ
    mapdh.v
    @23
    mapdh.n
    lspsncl
    syl2anc
    #
    @2
    @22
    @0
    @1
    cU
    @23
    @2
    eqid
    #
    lsmcl
    syl3anc
    wph
    @24
    @5
    @22
    wcel
    #
    @7
    @22
    wcel
    #
    @8
    @22
    wcel
    @27
    wph
    @24
    @4
    cV
    wcel
    #
    @36
    @27
    wph
    @24
    cX
    cV
    wcel
    #
    @28
    @38
    @27
    wph
    cX
    cV
    @29
    mapdhcl.x
    eldifad
    #
    @30
    c.mi
    cV
    cU
    cX
    cY
    mapdh.v
    mapdh.s
    lmodvsubcl
    syl3anc
    @22
    cN
    cV
    cU
    @4
    mapdh.v
    @23
    mapdh.n
    lspsncl
    syl2anc
    #
    wph
    @24
    @6
    cV
    wcel
    #
    @37
    @27
    wph
    @24
    @39
    @32
    @42
    @27
    @40
    @33
    c.mi
    cV
    cU
    cX
    cZ
    mapdh.v
    mapdh.s
    lmodvsubcl
    syl3anc
    @22
    cN
    cV
    cU
    @6
    mapdh.v
    @23
    mapdh.n
    lspsncl
    syl2anc
    #
    @2
    @22
    @5
    @7
    cU
    @23
    @35
    lsmcl
    syl3anc
    mapdin
    wph
    @20
    @14
    @21
    @17
    wph
    @20
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
    @22
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
    @23
    @35
    mapdh.c
    @13
    eqid
    #
    mapdh.k
    @31
    @34
    mapdlsm
    wph
    @44
    @11
    @45
    @12
    @13
    wph
    @44
    @11
    wceq
    #
    @5
    cM
    cfv
    #
    @15
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
    @47
    @49
    wa
    mapdh.eg
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
    mapdhe4.y
    wph
    @50
    cG
    cD
    mapdh.eg
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
    @30
    wph
    cX
    csn
    cN
    cfv
    #
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
    @30
    mapdhe.z
    @40
    mapdh.yz
    mapdh.xn
    lspindp2
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    @53
    mapdheq
    mpbid
    #
    simpld
    #
    wph
    @45
    @12
    wceq
    #
    @7
    cM
    cfv
    #
    @16
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
    @57
    @59
    wa
    mapdh.ee
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
    mapdhe.z
    wph
    @60
    cE
    cD
    mapdh.ee
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
    @33
    wph
    @51
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
    @52
    mapdhe4.y
    @33
    @40
    mapdh.yz
    mapdh.xn
    lspindp1
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    @61
    mapdheq
    mpbid
    #
    simpld
    #
    oveq12d
    eqtrd
    wph
    @21
    @48
    @58
    @13
    co
    @17
    wph
    cC
    @13
    @2
    @22
    cU
    cH
    cK
    cM
    cW
    @5
    @7
    mapdh.h
    mapdh.m
    mapdh.u
    @23
    @35
    mapdh.c
    @46
    mapdh.k
    @41
    @43
    mapdlsm
    wph
    @48
    @15
    @58
    @16
    @13
    wph
    @47
    @49
    @55
    simprd
    wph
    @57
    @59
    @63
    simprd
    oveq12d
    eqtrd
    ineq12d
    eqtrd
    wph
    @19
    @9
    cM
    wph
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
    @35
    mapdh.n
    @52
    @40
    mapdh.xn
    mapdh.yz
    mapdhe4.y
    mapdhe.z
    baerlem3
    fveq2d
    wph
    @13
    cR
    cJ
    cD
    cC
    cF
    cG
    cC
    c0g
    cfv
    #
    cE
    mapdh.d
    mapdh.r
    @65
    eqid
    #
    @46
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
    @40
    @30
    @54
    @56
    @33
    @62
    @64
    mapdh.xn
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
    @54
    @56
    @30
    @33
    @62
    @64
    mapdh.yz
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
    @65
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.j
    mapdh.k
    @54
    @56
    mapdhc.o
    @66
    mapdhe4.y
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
    @65
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.j
    mapdh.k
    @62
    @64
    mapdhc.o
    @66
    mapdhe.z
    mapdn0
    baerlem3
    3eqtr4d
end
