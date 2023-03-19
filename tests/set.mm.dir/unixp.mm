include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "wrel.mm"
include "wceq.mm"
include "relxp.mm"
include "relfld.mm"
include "ax-mp.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "xpeq1.mm"
include "0xp.mm"
include "dmxp.mm"
include "rnxp.mm"
include "uneq12.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "syl5eq.mm"

theorem unixp
  let cA: class A
  let cB: class B


  assert |- ( ( A X. B ) =/= (/) -> U. U. ( A X. B ) = ( A u. B ) )

  proof
    cA
    cB
    cxp
    #
    c0
    wne
    #
    @0
    cuni
    cuni
    #
    @0
    cdm
    #
    @0
    crn
    #
    cun
    #
    cA
    cB
    cun
    #
    @0
    wrel
    @2
    @5
    wceq
    cA
    cB
    relxp
    @0
    relfld
    ax-mp
    @1
    cB
    c0
    wne
    #
    cA
    c0
    wne
    #
    @5
    @6
    wceq
    #
    cB
    c0
    @0
    c0
    cB
    c0
    wceq
    @0
    cA
    c0
    cxp
    c0
    cB
    c0
    cA
    xpeq2
    cA
    xp0
    syl6eq
    necon3i
    cA
    c0
    @0
    c0
    cA
    c0
    wceq
    @0
    c0
    cB
    cxp
    c0
    cA
    c0
    cB
    xpeq1
    cB
    0xp
    syl6eq
    necon3i
    @7
    @3
    cA
    wceq
    @4
    cB
    wceq
    @9
    @8
    cA
    cB
    dmxp
    cA
    cB
    rnxp
    @3
    cA
    @4
    cB
    uneq12
    syl2an
    syl2anc
    syl5eq
end
