include "wcel.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "cfn.mm"
include "wss.mm"
include "wceq.mm"
include "com.mm"
include "1onn.mm"
include "ssid.mm"
include "ssnnfi.mm"
include "mp2an.mm"
include "enfii.mm"
include "mpan.mm"
include "adantl.mm"
include "snssi.mm"
include "adantr.mm"
include "ensn1g.mm"
include "ensym.mm"
include "entr.mm"
include "syl2an.mm"
include "fisseneq.mm"
include "syl3anc.mm"
include "eqcomd.mm"

theorem en1eqsn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. B /\ B ~~ 1o ) -> B = { A } )

  proof
    cA
    cB
    wcel
    #
    cB
    c1o
    cen
    wbr
    #
    wa
    #
    cA
    csn
    #
    cB
    @2
    cB
    cfn
    wcel
    #
    @3
    cB
    wss
    #
    @3
    cB
    cen
    wbr
    #
    @3
    cB
    wceq
    @1
    @4
    @0
    c1o
    cfn
    wcel
    #
    @1
    @4
    c1o
    com
    wcel
    c1o
    c1o
    wss
    @7
    1onn
    c1o
    ssid
    c1o
    c1o
    ssnnfi
    mp2an
    cB
    c1o
    enfii
    mpan
    adantl
    @0
    @5
    @1
    cA
    cB
    snssi
    adantr
    @0
    @3
    c1o
    cen
    wbr
    c1o
    cB
    cen
    wbr
    @6
    @1
    cA
    cB
    ensn1g
    cB
    c1o
    ensym
    @3
    c1o
    cB
    entr
    syl2an
    @3
    cB
    fisseneq
    syl3anc
    eqcomd
end
