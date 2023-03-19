include "cnpi.mm"
include "wcel.mm"
include "c1o.mm"
include "cop.mm"
include "cv.mm"
include "ceq.mm"
include "wbr.mm"
include "c2nd.mm"
include "cfv.mm"
include "clti.mm"
include "wn.mm"
include "wi.mm"
include "cxp.mm"
include "wral.mm"
include "crab.mm"
include "cnq.mm"
include "1pi.mm"
include "opelxpi.mm"
include "mpan2.mm"
include "nlt1pi.mm"
include "cvv.mm"
include "wceq.mm"
include "elexi.mm"
include "op2ndg.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "a1d.mm"
include "ralrimivw.mm"
include "breq1.mm"
include "fveq2.mm"
include "notbid.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "df-nq.mm"
include "syl6eleqr.mm"

theorem pinq
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. N. -> <. A , 1o >. e. Q. )

  proof
    cA
    cnpi
    wcel
    #
    cA
    c1o
    cop
    #
    vx
    cv
    #
    vy
    cv
    #
    ceq
    wbr
    #
    @3
    c2nd
    cfv
    #
    @2
    c2nd
    cfv
    #
    clti
    wbr
    #
    wn
    #
    wi
    #
    vy
    cnpi
    cnpi
    cxp
    #
    wral
    #
    vx
    @10
    crab
    #
    cnq
    @0
    @1
    @10
    wcel
    #
    @1
    @3
    ceq
    wbr
    #
    @5
    @1
    c2nd
    cfv
    #
    clti
    wbr
    #
    wn
    #
    wi
    #
    vy
    @10
    wral
    #
    @1
    @12
    wcel
    @0
    c1o
    cnpi
    wcel
    @13
    1pi
    cA
    c1o
    cnpi
    cnpi
    opelxpi
    mpan2
    @0
    @18
    vy
    @10
    @0
    @17
    @14
    @0
    @16
    @5
    c1o
    clti
    wbr
    @5
    nlt1pi
    @0
    @15
    c1o
    @5
    clti
    @0
    c1o
    cvv
    wcel
    @15
    c1o
    wceq
    c1o
    cnpi
    1pi
    elexi
    cA
    c1o
    cnpi
    cvv
    op2ndg
    mpan2
    breq2d
    mtbiri
    a1d
    ralrimivw
    @11
    @19
    vx
    @1
    @10
    @2
    @1
    wceq
    #
    @9
    @18
    vy
    @10
    @20
    @4
    @14
    @8
    @17
    @2
    @1
    @3
    ceq
    breq1
    @20
    @7
    @16
    @20
    @6
    @15
    @5
    clti
    @2
    @1
    c2nd
    fveq2
    breq2d
    notbid
    imbi12d
    ralbidv
    elrab
    sylanbrc
    vx
    vy
    df-nq
    syl6eleqr
end
