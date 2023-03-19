include "wne.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cres.mm"
include "cfv.mm"
include "resundir.mm"
include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "nelsn.mm"
include "ressnop0.mm"
include "syl.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "cvv.mm"
include "fvressn.mm"
include "fvprc.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "3eqtr3g.mm"

theorem fvunsn
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( B =/= D -> ( ( A u. { <. B , C >. } ) ` D ) = ( A ` D ) )

  proof
    cB
    cD
    wne
    #
    cD
    cA
    cB
    cC
    cop
    csn
    #
    cun
    #
    cD
    csn
    #
    cres
    #
    cfv
    #
    cD
    cA
    @3
    cres
    #
    cfv
    #
    cD
    @2
    cfv
    #
    cD
    cA
    cfv
    #
    @0
    cD
    @4
    @6
    @0
    @4
    @6
    @1
    @3
    cres
    #
    cun
    #
    @6
    cA
    @1
    @3
    resundir
    @0
    @11
    @6
    c0
    cun
    @6
    @0
    @10
    c0
    @6
    @0
    cB
    @3
    wcel
    wn
    @10
    c0
    wceq
    cB
    cD
    nelsn
    cB
    cC
    @3
    ressnop0
    syl
    uneq2d
    @6
    un0
    syl6eq
    syl5eq
    fveq1d
    cD
    cvv
    wcel
    #
    @5
    @8
    wceq
    @2
    cvv
    cD
    fvressn
    @12
    wn
    #
    @5
    c0
    @8
    cD
    @4
    fvprc
    cD
    @2
    fvprc
    eqtr4d
    pm2.61i
    @12
    @7
    @9
    wceq
    cA
    cvv
    cD
    fvressn
    @13
    @7
    c0
    @9
    cD
    @6
    fvprc
    cD
    cA
    fvprc
    eqtr4d
    pm2.61i
    3eqtr3g
end
