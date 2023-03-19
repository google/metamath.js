include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "dvhlvec.mm"
include "eldifad.mm"
include "lspindpi.mm"
include "simprd.mm"
include "necomd.mm"
include "neeqtrd.mm"
include "cpr.mm"
include "wcel.mm"
include "wss.mm"
include "sseq1d.mm"
include "clss.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "lspsnel5.mm"
include "3bitr4d.mm"
include "mtbid.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "cdif.mm"
include "simpr.mm"
include "prcom.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "lspexch.mm"
include "mtand.mm"
include "mapdh8aa.mm"

theorem mapdh8ab
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
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
  assume mapdh8a.h: |- H = ( LHyp ` K )
  assume mapdh8a.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh8a.v: |- V = ( Base ` U )
  assume mapdh8a.s: |- .- = ( -g ` U )
  assume mapdh8a.o: |- .0. = ( 0g ` U )
  assume mapdh8a.n: |- N = ( LSpan ` U )
  assume mapdh8a.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh8a.d: |- D = ( Base ` C )
  assume mapdh8a.r: |- R = ( -g ` C )
  assume mapdh8a.q: |- Q = ( 0g ` C )
  assume mapdh8a.j: |- J = ( LSpan ` C )
  assume mapdh8a.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh8a.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh8a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdh8ab.f: |- ( ph -> F e. D )
  assume mapdh8ab.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8ab.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8ab.ee: |- ( ph -> ( I ` <. X , F , Z >. ) = E )
  assume mapdh8ab.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8ab.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8ab.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh8ab.t: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8ab.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume mapdh8ab.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh8ab.yn: |- ( ph -> ( N ` { X } ) = ( N ` { T } ) )

  disjoint h x
  disjoint .- h
  disjoint .- x
  disjoint .0. h
  disjoint .0. x
  disjoint C h
  disjoint D h
  disjoint D x
  disjoint F h
  disjoint F x
  disjoint I h
  disjoint G h
  disjoint G x
  disjoint J h
  disjoint J x
  disjoint M h
  disjoint M x
  disjoint N h
  disjoint N x
  disjoint h ph
  disjoint R h
  disjoint R x
  disjoint Q x
  disjoint T h
  disjoint T x
  disjoint U h
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. Z , E , T >. ) )

  proof
    wph
    vx
    cC
    cD
    cQ
    cR
    cT
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
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.q
    mapdh8a.j
    mapdh8a.m
    mapdh8a.i
    mapdh8a.k
    mapdh8ab.f
    mapdh8ab.mn
    mapdh8ab.eg
    mapdh8ab.ee
    mapdh8ab.x
    mapdh8ab.y
    mapdh8ab.z
    wph
    cZ
    csn
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    cT
    csn
    cN
    cfv
    #
    wph
    @1
    @0
    wph
    @1
    cY
    csn
    cN
    cfv
    #
    wne
    @1
    @0
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    cZ
    mapdh8a.v
    mapdh8a.n
    wph
    cU
    cH
    cK
    cW
    mapdh8a.h
    mapdh8a.u
    mapdh8a.k
    dvhlvec
    #
    wph
    cX
    cV
    c.0
    csn
    #
    mapdh8ab.x
    eldifad
    #
    wph
    cY
    cV
    @5
    mapdh8ab.y
    eldifad
    #
    wph
    cZ
    cV
    @5
    mapdh8ab.z
    eldifad
    #
    mapdh8ab.xn
    lspindpi
    simprd
    necomd
    mapdh8ab.yn
    neeqtrd
    mapdh8ab.t
    wph
    cY
    cZ
    cT
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    cT
    cY
    cZ
    cpr
    cN
    cfv
    #
    wcel
    #
    wph
    cX
    @12
    wcel
    #
    @13
    mapdh8ab.xn
    wph
    @1
    @12
    wss
    @2
    @12
    wss
    @14
    @13
    wph
    @1
    @2
    @12
    mapdh8ab.yn
    sseq1d
    wph
    cU
    clss
    cfv
    #
    @12
    cN
    cV
    cU
    cX
    mapdh8a.v
    @15
    eqid
    #
    mapdh8a.n
    wph
    cU
    cH
    cK
    cW
    mapdh8a.h
    mapdh8a.u
    mapdh8a.k
    dvhlmod
    #
    wph
    @15
    cN
    cV
    cU
    cY
    cZ
    mapdh8a.v
    @16
    mapdh8a.n
    @17
    @7
    @8
    lspprcl
    #
    @6
    lspsnel5
    wph
    @15
    @12
    cN
    cV
    cU
    cT
    mapdh8a.v
    @16
    mapdh8a.n
    @17
    @18
    wph
    cT
    cV
    @5
    mapdh8ab.t
    eldifad
    #
    lspsnel5
    3bitr4d
    mtbid
    wph
    @11
    wa
    #
    cN
    cV
    cU
    cY
    cT
    c.0
    cZ
    mapdh8a.v
    mapdh8a.o
    mapdh8a.n
    wph
    cU
    clvec
    wcel
    @11
    @4
    adantr
    wph
    cY
    cV
    @5
    cdif
    wcel
    @11
    mapdh8ab.y
    adantr
    wph
    cT
    cV
    wcel
    @11
    @19
    adantr
    wph
    cZ
    cV
    wcel
    @11
    @8
    adantr
    wph
    @3
    @0
    wne
    @11
    mapdh8ab.yz
    adantr
    @20
    cY
    @10
    cT
    cZ
    cpr
    #
    cN
    cfv
    wph
    @11
    simpr
    @9
    @21
    cN
    cZ
    cT
    prcom
    fveq2i
    syl6eleq
    lspexch
    mtand
    mapdh8ab.xn
    mapdh8aa
end
