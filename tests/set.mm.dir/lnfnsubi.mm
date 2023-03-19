include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "cmv.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "neg1cn.mm"
include "lnfnaddmuli.mm"
include "mp3an1.mm"
include "hvsubval.mm"
include "fveq2d.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "mulm1.mm"
include "oveq2d.mm"
include "adantl.mm"
include "negsub.mm"
include "eqtr2d.mm"
include "syl2an.mm"
include "3eqtr4d.mm"

theorem lnfnsubi
  let cA: class A
  let cB: class B
  let cT: class T
  assume lnfnl.1: |- T e. LinFn


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( T ` ( A -h B ) ) = ( ( T ` A ) - ( T ` B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    c1
    cneg
    #
    cB
    csm
    co
    cva
    co
    #
    cT
    cfv
    #
    cA
    cT
    cfv
    #
    @3
    cB
    cT
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cA
    cB
    cmv
    co
    #
    cT
    cfv
    @6
    @7
    cmin
    co
    #
    @3
    cc
    wcel
    @0
    @1
    @5
    @9
    wceq
    neg1cn
    @3
    cA
    cB
    cT
    lnfnl.1
    lnfnaddmuli
    mp3an1
    @2
    @10
    @4
    cT
    cA
    cB
    hvsubval
    fveq2d
    @0
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @11
    @9
    wceq
    @1
    chil
    cc
    cA
    cT
    cT
    lnfnl.1
    lnfnfi
    #
    ffvelrni
    chil
    cc
    cB
    cT
    @14
    ffvelrni
    @12
    @13
    wa
    @9
    @6
    @7
    cneg
    #
    caddc
    co
    #
    @11
    @13
    @9
    @16
    wceq
    @12
    @13
    @8
    @15
    @6
    caddc
    @7
    mulm1
    oveq2d
    adantl
    @6
    @7
    negsub
    eqtr2d
    syl2an
    3eqtr4d
end
