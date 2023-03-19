include "co.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "mapdh6lem2N.mm"
include "oveq12d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "mapdh6lem1N.mm"
include "oveq2d.mm"
include "wcel.mm"
include "wne.mm"
include "cdif.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lmodindp1.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lcdlmod.mm"
include "cpr.mm"
include "wn.mm"
include "dvhlvec.mm"
include "lspindp2.mm"
include "simpld.mm"
include "mapdhcl.mm"
include "lspindp1.mm"
include "wss.mm"
include "clss.mm"
include "eqid.mm"
include "lspprcl.mm"
include "lspprvacl.mm"
include "lspsnel5a.mm"
include "lspsnel5.mm"
include "mtbid.mm"
include "nssne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "mapdheq.mm"
include "mpbir2and.mm"

theorem mapdh6aN
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
  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cX
    cF
    cY
    cZ
    c.pl
    co
    #
    cotp
    cI
    cfv
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cX
    cF
    cZ
    cotp
    cI
    cfv
    #
    c.pb
    co
    #
    wceq
    @0
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    @3
    csn
    #
    cJ
    cfv
    #
    wceq
    cX
    @0
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    #
    cF
    @3
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    wph
    @5
    cG
    cE
    c.pb
    co
    #
    csn
    #
    cJ
    cfv
    @7
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
    mapdh6lem2N
    wph
    @6
    @13
    cJ
    wph
    @3
    @12
    wph
    @1
    cG
    @2
    cE
    c.pb
    mapdh6.fg
    mapdh6.fe
    oveq12d
    #
    sneqd
    fveq2d
    eqtr4d
    wph
    @8
    cF
    @12
    cR
    co
    #
    csn
    #
    cJ
    cfv
    @11
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
    wph
    @10
    @16
    cJ
    wph
    @9
    @15
    wph
    @3
    @12
    cF
    cR
    @14
    oveq2d
    sneqd
    fveq2d
    eqtr4d
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    @3
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
    wcel
    #
    @0
    c.0
    wne
    @0
    cV
    c.0
    csn
    #
    cdif
    wcel
    wph
    cU
    clmod
    wcel
    cY
    cV
    wcel
    cZ
    cV
    wcel
    @17
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
    cY
    cV
    @18
    mapdhe6.y
    eldifad
    #
    wph
    cZ
    cV
    @18
    mapdhe6.z
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
    wph
    c.pl
    cN
    cV
    cU
    cY
    cZ
    c.0
    mapdh.v
    mapdh.p
    mapdhc.o
    mapdh.n
    @19
    @20
    @21
    mapdh6.yz
    lmodindp1
    @0
    cV
    c.0
    eldifsn
    sylanbrc
    wph
    cC
    clmod
    wcel
    @1
    cD
    wcel
    @2
    cD
    wcel
    @3
    cD
    wcel
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
    @20
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
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
    @20
    mapdhe6.z
    wph
    cX
    cV
    @18
    mapdhcl.x
    eldifad
    #
    mapdh6.yz
    mapdhe6.xn
    lspindp2
    simpld
    mapdhcl
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
    @21
    wph
    @22
    cZ
    csn
    cN
    cfv
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
    @23
    mapdhe6.y
    @21
    @24
    mapdh6.yz
    mapdhe6.xn
    lspindp1
    simpld
    mapdhcl
    c.pb
    cD
    cC
    @1
    @2
    mapdh.d
    mapdh.a
    lmodvacl
    syl3anc
    wph
    @4
    @22
    wph
    @4
    cY
    cZ
    cpr
    cN
    cfv
    #
    wss
    @22
    @25
    wss
    #
    wn
    @4
    @22
    wne
    wph
    cU
    clss
    cfv
    #
    @25
    cN
    cU
    @0
    @27
    eqid
    #
    mapdh.n
    @19
    wph
    @27
    cN
    cV
    cU
    cY
    cZ
    mapdh.v
    @28
    mapdh.n
    @19
    @20
    @21
    lspprcl
    #
    wph
    c.pl
    cN
    cV
    cU
    cY
    cZ
    mapdh.v
    mapdh.p
    mapdh.n
    @19
    @20
    @21
    lspprvacl
    lspsnel5a
    wph
    cX
    @25
    wcel
    @26
    mapdhe6.xn
    wph
    @27
    @25
    cN
    cV
    cU
    cX
    mapdh.v
    @28
    mapdh.n
    @19
    @29
    @24
    lspsnel5
    mtbid
    @4
    @22
    @25
    nssne2
    syl2anc
    necomd
    mapdheq
    mpbir2and
end
