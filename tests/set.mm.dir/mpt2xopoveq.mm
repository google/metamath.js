include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cvv.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "crab.mm"
include "wsbc.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2.mm"
include "op1stg.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "adantrr.mm"
include "wb.mm"
include "sbceq1a.mm"
include "adantl.mm"
include "bitrd.mm"
include "rabeqbidv.mm"
include "opex.mm"
include "simpr.mm"
include "rabexg.mm"
include "ad2antrr.mm"
include "weq.mm"
include "wnf.mm"
include "equid.mm"
include "nfvd.mm"
include "ax-mp.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfrab.mm"
include "nfsbc.mm"
include "ovmpt2dxf.mm"

theorem mpt2xopoveq
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vz: setvar z
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
  assert |- ( ( ( V e. X /\ W e. Y ) /\ K e. V ) -> ( <. V , W >. F K ) = { n e. V | [. <. V , W >. / x ]. [. K / y ]. ph } )

  proof
    cV
    cX
    wcel
    #
    cW
    cY
    wcel
    #
    wa
    #
    cK
    cV
    wcel
    #
    wa
    #
    vx
    vy
    cV
    cW
    cop
    #
    cK
    cvv
    vx
    cv
    #
    c1st
    cfv
    #
    wph
    vn
    @7
    crab
    #
    wph
    vy
    cK
    wsbc
    #
    vx
    @5
    wsbc
    #
    vn
    cV
    crab
    #
    cF
    cV
    cvv
    cF
    vx
    vy
    cvv
    @7
    @8
    cmpt2
    wceq
    @4
    mpt2xopoveq.f
    a1i
    @4
    @6
    @5
    wceq
    #
    vy
    cv
    cK
    wceq
    #
    wa
    #
    wa
    #
    wph
    @10
    vn
    @7
    cV
    @4
    @12
    @7
    cV
    wceq
    @13
    @12
    @4
    @7
    @5
    c1st
    cfv
    #
    cV
    @6
    @5
    c1st
    fveq2
    @2
    @16
    cV
    wceq
    @3
    cV
    cW
    cX
    cY
    op1stg
    adantr
    sylan9eqr
    #
    adantrr
    @15
    wph
    @9
    @10
    @14
    wph
    @9
    wb
    #
    @4
    @13
    @18
    @12
    wph
    vy
    cK
    sbceq1a
    adantl
    adantl
    @14
    @9
    @10
    wb
    #
    @4
    @12
    @19
    @13
    @9
    vx
    @5
    sbceq1a
    adantr
    adantl
    bitrd
    rabeqbidv
    @17
    @5
    cvv
    wcel
    @4
    cV
    cW
    opex
    a1i
    @2
    @3
    simpr
    @0
    @11
    cvv
    wcel
    @1
    @3
    @10
    vn
    cV
    cX
    rabexg
    ad2antrr
    vz
    vz
    weq
    #
    @4
    vx
    wnf
    vz
    equid
    #
    @20
    @4
    vx
    nfvd
    ax-mp
    @20
    @4
    vy
    wnf
    @21
    @20
    @4
    vy
    nfvd
    ax-mp
    vy
    @5
    nfcv
    #
    vx
    cK
    nfcv
    @10
    vx
    vn
    cV
    @9
    vx
    @5
    nfsbc1v
    vx
    cV
    nfcv
    nfrab
    @10
    vy
    vn
    cV
    @9
    vy
    vx
    @5
    @22
    wph
    vy
    cK
    nfsbc1v
    nfsbc
    vy
    cV
    nfcv
    nfrab
    ovmpt2dxf
end
