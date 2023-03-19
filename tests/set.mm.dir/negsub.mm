include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cmin.mm"
include "wceq.mm"
include "df-neg.mm"
include "oveq2i.mm"
include "a1i.mm"
include "0cn.mm"
include "addsubass.mm"
include "mp3an2.mm"
include "simpl.mm"
include "addid1d.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"

theorem negsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + -u B ) = ( A - B ) )

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
    cneg
    #
    caddc
    co
    #
    cA
    cc0
    cB
    cmin
    co
    #
    caddc
    co
    #
    cA
    cc0
    caddc
    co
    #
    cB
    cmin
    co
    #
    cA
    cB
    cmin
    co
    @4
    @6
    wceq
    @2
    @3
    @5
    cA
    caddc
    cB
    df-neg
    oveq2i
    a1i
    @0
    cc0
    cc
    wcel
    @1
    @8
    @6
    wceq
    0cn
    cA
    cc0
    cB
    addsubass
    mp3an2
    @2
    @7
    cA
    cB
    cmin
    @2
    cA
    @0
    @1
    simpl
    addid1d
    oveq1d
    3eqtr2d
end
