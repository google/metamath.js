include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "curry2.mm"
include "fveq1d.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
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
include "simpl.mm"
include "ndmovg.mm"
include "syl2an.mm"
include "eqtr4d.mm"
include "ex.mm"
include "adantr.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "pm2.61d2.mm"
include "eqtrd.mm"

theorem curry2val
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume curry2.1: |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) )


  assert |- ( ( F Fn ( A X. B ) /\ C e. B ) -> ( G ` D ) = ( D F C ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cC
    cB
    wcel
    #
    wa
    #
    cD
    cG
    cfv
    cD
    vx
    cA
    vx
    cv
    #
    cC
    cF
    co
    #
    cmpt
    #
    cfv
    #
    cD
    cC
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
    curry2.1
    curry2
    fveq1d
    @3
    cD
    cA
    wcel
    #
    @7
    @8
    wceq
    #
    @1
    @9
    wn
    #
    @10
    wi
    @2
    @1
    @11
    @10
    @1
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
    @1
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
    cA
    cD
    vx
    cA
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
    @1
    cF
    cdm
    @0
    wceq
    @9
    @2
    wa
    #
    wn
    @8
    c0
    wceq
    @11
    @0
    cF
    fndm
    @16
    @9
    @9
    @2
    simpl
    con3i
    cD
    cC
    cA
    cB
    cF
    ndmovg
    syl2an
    eqtr4d
    ex
    adantr
    vx
    cD
    @5
    @8
    cA
    @6
    @4
    cD
    cC
    cF
    oveq1
    @15
    cD
    cC
    cF
    ovex
    fvmpt
    pm2.61d2
    eqtrd
end
