include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wi.mm"
include "wral.mm"
include "rsp.mm"
include "sylbi.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem bnj590
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  assume bnj590.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )


  assert |- ( ( B = suc i /\ ps ) -> ( i e. _om -> ( B e. n -> ( f ` B ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) ) )

  proof
    cB
    vi
    cv
    #
    csuc
    #
    wceq
    #
    wps
    @0
    com
    wcel
    #
    cB
    vn
    cv
    #
    wcel
    #
    cB
    vf
    cv
    #
    cfv
    #
    vy
    @0
    @6
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    #
    wceq
    #
    wi
    #
    wi
    #
    wps
    @11
    @2
    @3
    @1
    @4
    wcel
    #
    @1
    @6
    cfv
    #
    @8
    wceq
    #
    wi
    #
    wi
    #
    wps
    @15
    vi
    com
    wral
    @16
    bnj590.1
    @15
    vi
    com
    rsp
    sylbi
    @2
    @10
    @15
    @3
    @2
    @5
    @12
    @9
    @14
    cB
    @1
    @4
    eleq1
    @2
    @7
    @13
    @8
    cB
    @1
    @6
    fveq2
    eqeq1d
    imbi12d
    imbi2d
    syl5ibr
    imp
end
