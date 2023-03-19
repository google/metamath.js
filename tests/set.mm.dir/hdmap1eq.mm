include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "eldifad.mm"
include "hdmap1val2.mm"
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

theorem hdmap1eq
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let cF: class F
  let cG: class G
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
  let vh: setvar h
  assume hdmap1val2.h: |- H = ( LHyp ` K )
  assume hdmap1val2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1val2.v: |- V = ( Base ` U )
  assume hdmap1val2.s: |- .- = ( -g ` U )
  assume hdmap1val2.o: |- .0. = ( 0g ` U )
  assume hdmap1val2.n: |- N = ( LSpan ` U )
  assume hdmap1val2.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1val2.d: |- D = ( Base ` C )
  assume hdmap1val2.r: |- R = ( -g ` C )
  assume hdmap1val2.l: |- L = ( LSpan ` C )
  assume hdmap1val2.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1val2.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1val2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1eq.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1eq.f: |- ( ph -> F e. D )
  assume hdmap1eq.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1eq.g: |- ( ph -> G e. D )
  assume hdmap1eq.e: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume hdmap1eq.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )


  assert |- ( ph -> ( ( I ` <. X , F , Y >. ) = G <-> ( ( M ` ( N ` { Y } ) ) = ( L ` { G } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( L ` { ( F R G ) } ) ) ) )

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
    cL
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
    cL
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
    cL
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
    cL
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
    cC
    cD
    cR
    cU
    vh
    cF
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
    cY
    c.0
    hdmap1val2.h
    hdmap1val2.u
    hdmap1val2.v
    hdmap1val2.s
    hdmap1val2.o
    hdmap1val2.n
    hdmap1val2.c
    hdmap1val2.d
    hdmap1val2.r
    hdmap1val2.l
    hdmap1val2.m
    hdmap1val2.i
    hdmap1val2.k
    wph
    cX
    cV
    c.0
    csn
    hdmap1eq.x
    eldifad
    hdmap1eq.f
    hdmap1eq.y
    hdmap1val2
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
    cL
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap1val2.h
    hdmap1val2.m
    hdmap1val2.u
    hdmap1val2.v
    hdmap1val2.s
    hdmap1val2.o
    hdmap1val2.n
    hdmap1val2.c
    hdmap1val2.d
    hdmap1val2.r
    hdmap1val2.l
    hdmap1val2.k
    hdmap1eq.x
    hdmap1eq.y
    hdmap1eq.f
    hdmap1eq.e
    hdmap1eq.mn
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
    hdmap1eq.g
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
    cL
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
    cL
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
