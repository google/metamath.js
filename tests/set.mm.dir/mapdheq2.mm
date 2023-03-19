include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "co.mm"
include "wa.mm"
include "mapdheq.mm"
include "adantr.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsnsub.mm"
include "fveq2d.mm"
include "lcdlmod.mm"
include "eqeq12d.mm"
include "biimpa.mm"
include "adantrl.mm"
include "chlt.mm"
include "wcel.mm"
include "simprl.mm"
include "cdif.mm"
include "wne.mm"
include "necomd.mm"
include "mpbir2and.mm"
include "ex.mm"
include "sylbid.mm"

theorem mapdheq2
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
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
  assume mapdhe.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdhe.g: |- ( ph -> G e. D )
  assume mapdh.ne2: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )

  disjoint G x
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
  disjoint h w
  assert |- ( ph -> ( ( I ` <. X , F , Y >. ) = G -> ( I ` <. Y , G , X >. ) = F ) )

  proof
    wph
    cX
    cF
    cY
    cotp
    cI
    cfv
    cG
    wceq
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    cG
    csn
    cJ
    cfv
    wceq
    #
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
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
    wceq
    #
    wa
    #
    cY
    cG
    cX
    cotp
    cI
    cfv
    cF
    wceq
    #
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
    mapdhe.y
    mapdhe.g
    mapdh.ne2
    mapdheq
    wph
    @6
    @7
    wph
    @6
    wa
    #
    @7
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    #
    cY
    cX
    c.mi
    co
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cG
    cF
    cR
    co
    csn
    cJ
    cfv
    #
    wceq
    #
    wph
    @10
    @6
    mapdh.mn
    adantr
    wph
    @5
    @14
    @1
    wph
    @5
    @14
    wph
    @3
    @12
    @4
    @13
    wph
    @2
    @11
    cM
    wph
    c.mi
    cN
    cV
    cU
    cX
    cY
    mapdh.v
    mapdh.s
    mapdh.n
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlmod
    wph
    cX
    cV
    c.0
    csn
    #
    mapdhcl.x
    eldifad
    wph
    cY
    cV
    @15
    mapdhe.y
    eldifad
    lspsnsub
    fveq2d
    wph
    cR
    cJ
    cD
    cC
    cF
    cG
    mapdh.d
    mapdh.r
    mapdh.j
    wph
    cC
    cH
    cK
    cW
    mapdh.h
    mapdh.c
    mapdh.k
    lcdlmod
    mapdhc.f
    mapdhe.g
    lspsnsub
    eqeq12d
    biimpa
    adantrl
    @8
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cG
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
    cY
    cX
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
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @6
    mapdh.k
    adantr
    wph
    cG
    cD
    wcel
    @6
    mapdhe.g
    adantr
    wph
    @1
    @5
    simprl
    wph
    cY
    cV
    @15
    cdif
    #
    wcel
    @6
    mapdhe.y
    adantr
    wph
    cX
    @16
    wcel
    @6
    mapdhcl.x
    adantr
    wph
    cF
    cD
    wcel
    @6
    mapdhc.f
    adantr
    wph
    @0
    @9
    wne
    @6
    wph
    @9
    @0
    mapdh.ne2
    necomd
    adantr
    mapdheq
    mpbir2and
    ex
    sylbid
end
