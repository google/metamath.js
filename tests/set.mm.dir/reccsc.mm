include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "ccsc.mm"
include "cdiv.mm"
include "co.mm"
include "cscval.mm"
include "oveq2d.mm"
include "wceq.mm"
include "sincl.mm"
include "recrec.mm"
include "sylan.mm"
include "eqtr2d.mm"

theorem reccsc
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) -> ( sin ` A ) = ( 1 / ( csc ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    csin
    cfv
    #
    cc0
    wne
    #
    wa
    #
    c1
    cA
    ccsc
    cfv
    #
    cdiv
    co
    c1
    c1
    @1
    cdiv
    co
    #
    cdiv
    co
    #
    @1
    @3
    @4
    @5
    c1
    cdiv
    cA
    cscval
    oveq2d
    @0
    @1
    cc
    wcel
    @2
    @6
    @1
    wceq
    cA
    sincl
    @1
    recrec
    sylan
    eqtr2d
end
