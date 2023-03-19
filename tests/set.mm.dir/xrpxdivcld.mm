include "cc0.mm"
include "wceq.mm"
include "cxdiv.mm"
include "co.mm"
include "cpnf.mm"
include "cicc.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "oveq1.mm"
include "xdiv0rp.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "w3o.mm"
include "elxrge02.mm"
include "biimpri.mm"
include "3o1cs.mm"
include "simpr.mm"
include "adantr.mm"
include "rpxdivcld.mm"
include "3o2cs.mm"
include "xdivpnfrp.mm"
include "3o3cs.mm"
include "sylib.mm"
include "mpjao3dan.mm"

theorem xrpxdivcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrpxdivcld.1: |- ( ph -> A e. ( 0 [,] +oo ) )
  assume xrpxdivcld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A /e B ) e. ( 0 [,] +oo ) )

  proof
    wph
    cA
    cc0
    wceq
    #
    cA
    cB
    cxdiv
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cA
    crp
    wcel
    #
    cA
    cpnf
    wceq
    #
    wph
    @0
    wa
    @1
    cc0
    wceq
    #
    @3
    @0
    wph
    @1
    cc0
    cB
    cxdiv
    co
    #
    cc0
    cA
    cc0
    cB
    cxdiv
    oveq1
    wph
    cB
    crp
    wcel
    #
    @7
    cc0
    wceq
    xrpxdivcld.2
    cB
    xdiv0rp
    syl
    sylan9eqr
    @6
    @1
    crp
    wcel
    #
    @1
    cpnf
    wceq
    #
    @3
    @3
    @6
    @9
    @10
    w3o
    @1
    elxrge02
    biimpri
    #
    3o1cs
    syl
    wph
    @4
    wa
    #
    @9
    @3
    @12
    cA
    cB
    wph
    @4
    simpr
    wph
    @8
    @4
    xrpxdivcld.2
    adantr
    rpxdivcld
    @6
    @9
    @10
    @3
    @11
    3o2cs
    syl
    wph
    @5
    wa
    @10
    @3
    @5
    wph
    @1
    cpnf
    cB
    cxdiv
    co
    #
    cpnf
    cA
    cpnf
    cB
    cxdiv
    oveq1
    wph
    @8
    @13
    cpnf
    wceq
    xrpxdivcld.2
    cB
    xdivpnfrp
    syl
    sylan9eqr
    @6
    @9
    @10
    @3
    @11
    3o3cs
    syl
    wph
    cA
    @2
    wcel
    @0
    @4
    @5
    w3o
    xrpxdivcld.1
    cA
    elxrge02
    sylib
    mpjao3dan
end
