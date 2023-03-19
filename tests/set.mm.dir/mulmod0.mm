include "cz.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "cdiv.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "rpcn.mm"
include "adantl.mm"
include "wne.mm"
include "rpne0.mm"
include "divcan4d.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "rpre.mm"
include "remulcl.mm"
include "syl2an.mm"
include "mod0.mm"
include "sylancom.mm"
include "mpbird.mm"

theorem mulmod0
  let cA: class A
  let cM: class M


  assert |- ( ( A e. ZZ /\ M e. RR+ ) -> ( ( A x. M ) mod M ) = 0 )

  proof
    cA
    cz
    wcel
    #
    cM
    crp
    wcel
    #
    wa
    #
    cA
    cM
    cmul
    co
    #
    cM
    cmo
    co
    cc0
    wceq
    #
    @3
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    @2
    @5
    cA
    cz
    @2
    cA
    cM
    @0
    cA
    cc
    wcel
    @1
    cA
    zcn
    adantr
    @1
    cM
    cc
    wcel
    @0
    cM
    rpcn
    adantl
    @1
    cM
    cc0
    wne
    @0
    cM
    rpne0
    adantl
    divcan4d
    @0
    @1
    simpl
    eqeltrd
    @0
    @1
    @3
    cr
    wcel
    #
    @4
    @6
    wb
    @0
    cA
    cr
    wcel
    cM
    cr
    wcel
    @7
    @1
    cA
    zre
    cM
    rpre
    cA
    cM
    remulcl
    syl2an
    @3
    cM
    mod0
    sylancom
    mpbird
end
