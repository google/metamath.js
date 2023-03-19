include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cmv.mm"
include "cc.mm"
include "wceq.mm"
include "neg1cn.mm"
include "lnopaddmuli.mm"
include "mp3an1.mm"
include "hvsubval.mm"
include "fveq2d.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "syl2an.mm"
include "3eqtr4d.mm"

theorem lnopsubi
  let cA: class A
  let cB: class B
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( T ` ( A -h B ) ) = ( ( T ` A ) -h ( T ` B ) ) )

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
    csm
    co
    cva
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
    cmv
    co
    #
    @3
    cc
    wcel
    @0
    @1
    @5
    @8
    wceq
    neg1cn
    @3
    cA
    cB
    cT
    lnopl.1
    lnopaddmuli
    mp3an1
    @2
    @9
    @4
    cT
    cA
    cB
    hvsubval
    fveq2d
    @0
    @6
    chil
    wcel
    @7
    chil
    wcel
    @10
    @8
    wceq
    @1
    chil
    chil
    cA
    cT
    cT
    lnopl.1
    lnopfi
    #
    ffvelrni
    chil
    chil
    cB
    cT
    @11
    ffvelrni
    @6
    @7
    hvsubval
    syl2an
    3eqtr4d
end
