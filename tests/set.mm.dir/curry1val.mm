include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "curry1.mm"
include "fveq1d.mm"
include "wceq.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "eqid.mm"
include "dmmptss.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "adantl.mm"
include "fndm.mm"
include "adantr.mm"
include "simpr.mm"
include "ndmovg.mm"
include "syl2an.mm"
include "eqtr4d.mm"
include "ex.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "pm2.61d2.mm"
include "eqtrd.mm"

theorem curry1val
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume curry1.1: |- G = ( F o. `' ( 2nd |` ( { C } X. _V ) ) )


  assert |- ( ( F Fn ( A X. B ) /\ C e. A ) -> ( G ` D ) = ( C F D ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cC
    cA
    wcel
    #
    wa
    #
    cD
    cG
    cfv
    cD
    vx
    cB
    cC
    vx
    cv
    #
    cF
    co
    #
    cmpt
    #
    cfv
    #
    cC
    cD
    cF
    co
    #
    @3
    cD
    cG
    @6
    vx
    cA
    cB
    cC
    cF
    cG
    curry1.1
    curry1
    fveq1d
    @3
    cD
    cB
    wcel
    #
    @7
    @8
    wceq
    #
    @3
    @9
    wn
    #
    @10
    @3
    @11
    wa
    @7
    c0
    @8
    @11
    @7
    c0
    wceq
    #
    @3
    @11
    cD
    @6
    cdm
    #
    wcel
    #
    wn
    @12
    @14
    @9
    @13
    cB
    cD
    vx
    cB
    @5
    @6
    @6
    eqid
    #
    dmmptss
    sseli
    con3i
    cD
    @6
    ndmfv
    syl
    adantl
    @3
    cF
    cdm
    @0
    wceq
    #
    @2
    @9
    wa
    #
    wn
    @8
    c0
    wceq
    @11
    @1
    @16
    @2
    @0
    cF
    fndm
    adantr
    @17
    @9
    @2
    @9
    simpr
    con3i
    cC
    cD
    cA
    cB
    cF
    ndmovg
    syl2an
    eqtr4d
    ex
    vx
    cD
    @5
    @8
    cB
    @6
    @4
    cD
    cC
    cF
    oveq2
    @15
    cC
    cD
    cF
    ovex
    fvmpt
    pm2.61d2
    eqtrd
end
