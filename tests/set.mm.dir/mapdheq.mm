include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cdif.mm"
include "mapdhval2.mm"
include "eqeq1d.mm"
include "wreu.mm"
include "wb.mm"
include "mapdpg.mm"
include "nfv.mm"
include "nfcvd.mm"
include "nfvd.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "sneqd.mm"
include "anbi12d.mm"
include "adantl.mm"
include "riota2df.mm"
include "mpdan.mm"
include "bitr4d.mm"

theorem mapdheq
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
  assert |- ( ph -> ( ( I ` <. X , F , Y >. ) = G <-> ( ( M ` ( N ` { Y } ) ) = ( J ` { G } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( F R G ) } ) ) ) )

  proof
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
    cY
    csn
    cN
    cfv
    cM
    cfv
    #
    vh
    cv
    #
    csn
    #
    cJ
    cfv
    #
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
    #
    cF
    @2
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cG
    wceq
    #
    @1
    cG
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    @6
    cF
    cG
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    wph
    @0
    @12
    cG
    wph
    vx
    cV
    c.0
    csn
    cdif
    cD
    cC
    cD
    cQ
    cR
    vh
    cF
    cI
    cJ
    cM
    c.mi
    cN
    cV
    cX
    cY
    c.0
    mapdh.q
    mapdh.i
    mapdhcl.x
    mapdhc.f
    mapdhe.y
    mapdhval2
    eqeq1d
    wph
    @11
    vh
    cD
    wreu
    @21
    @13
    wb
    wph
    cC
    cR
    cU
    vh
    cD
    cF
    cH
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
    mapdhcl.x
    mapdhe.y
    mapdhc.f
    mapdh.ne2
    mapdh.mn
    mapdpg
    wph
    @11
    @21
    vh
    cD
    cG
    wph
    vh
    nfv
    wph
    vh
    cG
    nfcvd
    wph
    @21
    vh
    nfvd
    mapdhe.g
    @2
    cG
    wceq
    #
    @11
    @21
    wb
    wph
    @22
    @5
    @16
    @10
    @20
    @22
    @4
    @15
    @1
    @22
    @3
    @14
    cJ
    @2
    cG
    sneq
    fveq2d
    eqeq2d
    @22
    @9
    @19
    @6
    @22
    @8
    @18
    cJ
    @22
    @7
    @17
    @2
    cG
    cF
    cR
    oveq2
    sneqd
    fveq2d
    eqeq2d
    anbi12d
    adantl
    riota2df
    mpdan
    bitr4d
end
