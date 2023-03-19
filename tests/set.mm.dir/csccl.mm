include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ccsc.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cscval.mm"
include "sincl.mm"
include "adantr.mm"
include "simpr.mm"
include "reccld.mm"
include "eqeltrd.mm"

theorem csccl
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) -> ( csc ` A ) e. CC )

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
    cA
    ccsc
    cfv
    c1
    @1
    cdiv
    co
    cc
    cA
    cscval
    @3
    @1
    @0
    @1
    cc
    wcel
    @2
    cA
    sincl
    adantr
    @0
    @2
    simpr
    reccld
    eqeltrd
end
