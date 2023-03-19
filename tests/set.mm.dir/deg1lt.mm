include "wcel.mm"
include "cn0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "simp3.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "simp2.mm"
include "cle.mm"
include "cxr.mm"
include "deg1xrcl.mm"
include "3ad2ant1.mm"
include "xrleid.mm"
include "syl.mm"
include "wb.mm"
include "simp1.mm"
include "deg1leb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "breq2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "mpd.mm"

theorem deg1lt
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vb: setvar b
  let va: setvar a
  assume deg1leb.d: |- D = ( deg1 ` R )
  assume deg1leb.p: |- P = ( Poly1 ` R )
  assume deg1leb.b: |- B = ( Base ` P )
  assume deg1leb.y: |- .0. = ( 0g ` R )
  assume deg1leb.a: |- A = ( coe1 ` F )


  assert |- ( ( F e. B /\ G e. NN0 /\ ( D ` F ) < G ) -> ( A ` G ) = .0. )

  proof
    cF
    cB
    wcel
    #
    cG
    cn0
    wcel
    #
    cF
    cD
    cfv
    #
    cG
    clt
    wbr
    #
    w3a
    #
    @3
    cG
    cA
    cfv
    #
    c.0
    wceq
    #
    @0
    @1
    @3
    simp3
    @4
    @1
    @2
    vx
    cv
    #
    clt
    wbr
    #
    @7
    cA
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @3
    @6
    wi
    #
    @0
    @1
    @3
    simp2
    @4
    @2
    @2
    cle
    wbr
    #
    @12
    @4
    @2
    cxr
    wcel
    #
    @14
    @0
    @1
    @15
    @3
    cB
    cD
    cP
    cR
    cF
    deg1leb.d
    deg1leb.p
    deg1leb.b
    deg1xrcl
    3ad2ant1
    #
    @2
    xrleid
    syl
    @4
    @0
    @15
    @14
    @12
    wb
    @0
    @1
    @3
    simp1
    @16
    vx
    cA
    cB
    cD
    cP
    cR
    cF
    @2
    c.0
    deg1leb.d
    deg1leb.p
    deg1leb.b
    deg1leb.y
    deg1leb.a
    deg1leb
    syl2anc
    mpbid
    @11
    @13
    vx
    cG
    cn0
    @7
    cG
    wceq
    #
    @8
    @3
    @10
    @6
    @7
    cG
    @2
    clt
    breq2
    @17
    @9
    @5
    c.0
    @7
    cG
    cA
    fveq2
    eqeq1d
    imbi12d
    rspcva
    syl2anc
    mpd
end
