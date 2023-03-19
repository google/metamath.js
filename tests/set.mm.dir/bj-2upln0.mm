include "bj-c2uple.mm"
include "bj-c1upl.mm"
include "c1o.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "cun.mm"
include "c0.mm"
include "df-bj-2upl.mm"
include "wpss.mm"
include "wne.mm"
include "wss.mm"
include "bj-1upln0.mm"
include "0pss.mm"
include "mpbir.mm"
include "ssun1.mm"
include "psssstr.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqnetri.mm"

theorem bj-2upln0
  let cA: class A
  let cB: class B


  assert |- (| A ,, B |) =/= (/)

  proof
    cA
    cB
    bj-c2uple
    cA
    bj-c1upl
    #
    c1o
    csn
    cB
    bj-ctag
    cxp
    #
    cun
    #
    c0
    cA
    cB
    df-bj-2upl
    c0
    @2
    wpss
    #
    @2
    c0
    wne
    c0
    @0
    wpss
    #
    @0
    @2
    wss
    @3
    @4
    @0
    c0
    wne
    cA
    bj-1upln0
    @0
    0pss
    mpbir
    @0
    @1
    ssun1
    c0
    @0
    @2
    psssstr
    mp2an
    @2
    0pss
    mpbi
    eqnetri
end
