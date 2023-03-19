include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cs1.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "simpr.mm"
include "s1len.mm"
include "syl6eqr.mm"
include "csn.mm"
include "cvv.mm"
include "fvex.mm"
include "s1fv.mm"
include "eqcomd.mm"
include "mp1i.mm"
include "c0ex.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "ralsn.mm"
include "sylibr.mm"
include "oveq2.mm"
include "adantl.mm"
include "fzo01.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "wb.mm"
include "cn.mm"
include "1nn.mm"
include "fstwrdne0.mm"
include "mpan.mm"
include "s1cld.mm"
include "eqwrd.mm"
include "syldan.mm"
include "mpbir2and.mm"

theorem eqs1
  let cA: class A
  let cW: class W
  let vx: setvar x


  assert |- ( ( W e. Word A /\ ( # ` W ) = 1 ) -> W = <" ( W ` 0 ) "> )

  proof
    cW
    cA
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cW
    cc0
    cW
    cfv
    #
    cs1
    #
    wceq
    #
    @2
    @6
    chash
    cfv
    #
    wceq
    #
    vx
    cv
    #
    cW
    cfv
    #
    @10
    @6
    cfv
    #
    wceq
    #
    vx
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    @4
    @2
    c1
    @8
    @1
    @3
    simpr
    @5
    s1len
    syl6eqr
    @4
    @15
    @13
    vx
    cc0
    csn
    #
    wral
    #
    @4
    @5
    cc0
    @6
    cfv
    #
    wceq
    #
    @17
    @5
    cvv
    wcel
    #
    @19
    @4
    cc0
    cW
    fvex
    @20
    @18
    @5
    @5
    cvv
    s1fv
    eqcomd
    mp1i
    @13
    @19
    vx
    cc0
    c0ex
    @10
    cc0
    wceq
    @11
    @5
    @12
    @18
    @10
    cc0
    cW
    fveq2
    @10
    cc0
    @6
    fveq2
    eqeq12d
    ralsn
    sylibr
    @4
    @13
    vx
    @14
    @16
    @4
    @14
    cc0
    c1
    cfzo
    co
    #
    @16
    @3
    @14
    @21
    wceq
    @1
    @2
    c1
    cc0
    cfzo
    oveq2
    adantl
    fzo01
    syl6eq
    raleqdv
    mpbird
    @1
    @3
    @6
    @0
    wcel
    @7
    @9
    @15
    wa
    wb
    @4
    @5
    cA
    c1
    cn
    wcel
    @4
    @5
    cA
    wcel
    1nn
    c1
    cA
    cW
    fstwrdne0
    mpan
    s1cld
    cW
    vx
    cA
    @6
    eqwrd
    syldan
    mpbir2and
end
