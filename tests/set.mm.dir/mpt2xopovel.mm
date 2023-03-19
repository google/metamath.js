include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "co.mm"
include "wsbc.mm"
include "w3a.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "crab.mm"
include "mpt2xopn0yelv.mm"
include "pm4.71rd.mm"
include "mpt2xopoveq.mm"
include "eleq2d.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "sbccom.mm"
include "sbcbii.mm"
include "bitri.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem mpt2xopovel
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mpt2xopoveq.f: |- F = ( x e. _V , y e. ( 1st ` x ) |-> { n e. ( 1st ` x ) | ph } )

  disjoint K n
  disjoint K x
  disjoint K y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint V n
  disjoint V x
  disjoint V y
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint N x
  disjoint N y
  assert |- ( ( V e. X /\ W e. Y ) -> ( N e. ( <. V , W >. F K ) <-> ( K e. V /\ N e. V /\ [. <. V , W >. / x ]. [. K / y ]. [. N / n ]. ph ) ) )

  proof
    cV
    cX
    wcel
    cW
    cY
    wcel
    wa
    #
    cN
    cV
    cW
    cop
    #
    cK
    cF
    co
    #
    wcel
    #
    cK
    cV
    wcel
    #
    @3
    wa
    #
    @4
    cN
    cV
    wcel
    #
    wph
    vn
    cN
    wsbc
    vy
    cK
    wsbc
    #
    vx
    @1
    wsbc
    #
    w3a
    #
    @0
    @3
    @4
    vx
    vy
    wph
    vn
    vx
    cv
    c1st
    cfv
    crab
    cF
    cK
    cN
    cV
    cW
    cX
    cY
    mpt2xopoveq.f
    mpt2xopn0yelv
    pm4.71rd
    @0
    @5
    @4
    @6
    @8
    wa
    #
    wa
    @9
    @0
    @4
    @3
    @10
    @0
    @4
    wa
    #
    @3
    cN
    wph
    vy
    cK
    wsbc
    #
    vx
    @1
    wsbc
    #
    vn
    cV
    crab
    #
    wcel
    #
    @10
    @11
    @2
    @14
    cN
    wph
    vx
    vy
    vn
    cF
    cK
    cV
    cW
    cX
    cY
    mpt2xopoveq.f
    mpt2xopoveq
    eleq2d
    @15
    @6
    @13
    vn
    cN
    wsbc
    #
    wa
    @10
    @13
    vn
    cN
    cV
    vn
    cV
    nfcv
    elrabsf
    @16
    @8
    @6
    @16
    @12
    vn
    cN
    wsbc
    #
    vx
    @1
    wsbc
    @8
    @12
    vn
    vx
    cN
    @1
    sbccom
    @17
    @7
    vx
    @1
    wph
    vn
    vy
    cN
    cK
    sbccom
    sbcbii
    bitri
    anbi2i
    bitri
    syl6bb
    pm5.32da
    @4
    @6
    @8
    3anass
    syl6bbr
    bitrd
end
