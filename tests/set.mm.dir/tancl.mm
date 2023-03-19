include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ctan.mm"
include "csin.mm"
include "cdiv.mm"
include "co.mm"
include "tanval.mm"
include "sincl.mm"
include "adantr.mm"
include "coscl.mm"
include "simpr.mm"
include "divcld.mm"
include "eqeltrd.mm"

theorem tancl
  let cA: class A


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( tan ` A ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    ctan
    cfv
    cA
    csin
    cfv
    #
    @1
    cdiv
    co
    cc
    cA
    tanval
    @3
    @4
    @1
    @0
    @4
    cc
    wcel
    @2
    cA
    sincl
    adantr
    @0
    @1
    cc
    wcel
    @2
    cA
    coscl
    adantr
    @0
    @2
    simpr
    divcld
    eqeltrd
end
