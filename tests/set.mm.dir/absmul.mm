include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "csqrt.mm"
include "cabs.mm"
include "cjmul.mm"
include "oveq2d.mm"
include "simpl.mm"
include "simpr.mm"
include "cjcld.mm"
include "mul4d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cjmulrcl.mm"
include "cjmulge0.mm"
include "jca.mm"
include "sqrtmul.mm"
include "syl2an.mm"
include "mulcl.mm"
include "absval.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"

theorem absmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( abs ` ( A x. B ) ) = ( ( abs ` A ) x. ( abs ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    @3
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    cB
    cB
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    @3
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    cmul
    co
    @2
    @6
    @8
    @11
    cmul
    co
    #
    csqrt
    cfv
    #
    @13
    @2
    @5
    @17
    csqrt
    @2
    @5
    @3
    @7
    @10
    cmul
    co
    #
    cmul
    co
    @17
    @2
    @4
    @19
    @3
    cmul
    cA
    cB
    cjmul
    oveq2d
    @2
    cA
    cB
    @7
    @10
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @2
    cA
    @20
    cjcld
    @2
    cB
    @21
    cjcld
    mul4d
    eqtrd
    fveq2d
    @0
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    wa
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    wa
    @18
    @13
    wceq
    @1
    @0
    @22
    @23
    cA
    cjmulrcl
    cA
    cjmulge0
    jca
    @1
    @24
    @25
    cB
    cjmulrcl
    cB
    cjmulge0
    jca
    @8
    @11
    sqrtmul
    syl2an
    eqtrd
    @2
    @3
    cc
    wcel
    @14
    @6
    wceq
    cA
    cB
    mulcl
    @3
    absval
    syl
    @0
    @1
    @15
    @9
    @16
    @12
    cmul
    cA
    absval
    cB
    absval
    oveqan12d
    3eqtr4d
end
