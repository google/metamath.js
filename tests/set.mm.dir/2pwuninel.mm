include "cuni.mm"
include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "wn.mm"
include "csdm.mm"
include "wbr.mm"
include "sdomirr.mm"
include "wss.mm"
include "elssuni.mm"
include "cdom.mm"
include "ssdomg.mm"
include "canth2g.mm"
include "pwexb.mm"
include "sylbi.mm"
include "sdomtr.mm"
include "syl2anc.mm"
include "domsdomtr.mm"
include "ex.mm"
include "syl6ci.mm"
include "syl5.mm"
include "mtoi.mm"
include "elex.mm"
include "bitri.mm"
include "sylibr.mm"
include "con3i.mm"
include "pm2.61i.mm"

theorem 2pwuninel
  let cA: class A


  assert |- -. ~P ~P U. A e. A

  proof
    cA
    cuni
    #
    cvv
    wcel
    #
    @0
    cpw
    #
    cpw
    #
    cA
    wcel
    #
    wn
    @1
    @4
    @3
    @3
    csdm
    wbr
    #
    @3
    sdomirr
    @4
    @3
    @0
    wss
    #
    @1
    @5
    @3
    cA
    elssuni
    @1
    @6
    @3
    @0
    cdom
    wbr
    #
    @0
    @3
    csdm
    wbr
    #
    @5
    @3
    @0
    cvv
    ssdomg
    @1
    @0
    @2
    csdm
    wbr
    @2
    @3
    csdm
    wbr
    #
    @8
    @0
    cvv
    canth2g
    @1
    @2
    cvv
    wcel
    #
    @9
    @0
    pwexb
    #
    @2
    cvv
    canth2g
    sylbi
    @0
    @2
    @3
    sdomtr
    syl2anc
    @7
    @8
    @5
    @3
    @0
    @3
    domsdomtr
    ex
    syl6ci
    syl5
    mtoi
    @4
    @1
    @4
    @3
    cvv
    wcel
    #
    @1
    @3
    cA
    elex
    @1
    @10
    @12
    @11
    @2
    pwexb
    bitri
    sylibr
    con3i
    pm2.61i
end
