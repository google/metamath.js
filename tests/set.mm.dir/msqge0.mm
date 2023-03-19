include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "oveq12.mm"
include "anidms.mm"
include "0cn.mm"
include "mul01i.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "wne.mm"
include "wa.mm"
include "0red.mm"
include "simpl.mm"
include "remulcld.mm"
include "msqgt0.mm"
include "ltled.mm"
include "0re.mm"
include "leid.mm"
include "mp1i.mm"
include "pm2.61ne.mm"

theorem msqge0
  let cA: class A


  assert |- ( A e. RR -> 0 <_ ( A x. A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cA
    cmul
    co
    #
    cle
    wbr
    cc0
    cc0
    cle
    wbr
    #
    cA
    cc0
    cA
    cc0
    wceq
    #
    @1
    cc0
    cc0
    cle
    @3
    @1
    cc0
    cc0
    cmul
    co
    #
    cc0
    @3
    @1
    @4
    wceq
    cA
    cc0
    cA
    cc0
    cmul
    oveq12
    anidms
    cc0
    0cn
    mul01i
    syl6eq
    breq2d
    @0
    cA
    cc0
    wne
    #
    wa
    #
    cc0
    @1
    @6
    0red
    @6
    cA
    cA
    @0
    @5
    simpl
    #
    @7
    remulcld
    cA
    msqgt0
    ltled
    cc0
    cr
    wcel
    @2
    @0
    0re
    cc0
    leid
    mp1i
    pm2.61ne
end
