include "cv.mm"
include "cop.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cnr.mm"
include "c0r.mm"
include "csn.mm"
include "cr.mm"
include "df-r.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "elsni.mm"
include "c1r.mm"
include "df-1.mm"
include "oveq2i.mm"
include "cmr.mm"
include "1sr.mm"
include "mulresr.mm"
include "mpan2.mm"
include "1idsr.mm"
include "opeq1d.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "opeq2.mm"
include "oveq1d.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "sylan2.mm"
include "optocl.mm"

theorem ax1rid
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. RR -> ( A x. 1 ) = A )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    c1
    cmul
    co
    #
    @2
    wceq
    #
    cA
    c1
    cmul
    co
    #
    cA
    wceq
    vx
    vy
    cA
    cnr
    c0r
    csn
    #
    cr
    df-r
    @2
    cA
    wceq
    #
    @3
    @5
    @2
    cA
    @2
    cA
    c1
    cmul
    oveq1
    @7
    id
    eqeq12d
    @1
    @6
    wcel
    @0
    cnr
    wcel
    #
    @1
    c0r
    wceq
    #
    @4
    @1
    c0r
    elsni
    @9
    @8
    @4
    @8
    @4
    @9
    @0
    c0r
    cop
    #
    c1
    cmul
    co
    #
    @10
    wceq
    @8
    @11
    @10
    c1r
    c0r
    cop
    #
    cmul
    co
    #
    @10
    c1
    @12
    @10
    cmul
    df-1
    oveq2i
    @8
    @13
    @0
    c1r
    cmr
    co
    #
    c0r
    cop
    #
    @10
    @8
    c1r
    cnr
    wcel
    @13
    @15
    wceq
    1sr
    @0
    c1r
    mulresr
    mpan2
    @8
    @14
    @0
    c0r
    @0
    1idsr
    opeq1d
    eqtrd
    syl5eq
    @9
    @3
    @11
    @2
    @10
    @9
    @2
    @10
    c1
    cmul
    @1
    c0r
    @0
    opeq2
    #
    oveq1d
    @16
    eqeq12d
    syl5ibr
    impcom
    sylan2
    optocl
end
