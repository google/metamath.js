include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "crp.mm"
include "peano2re.mm"
include "adantr.mm"
include "0red.mm"
include "simpl.mm"
include "simpr.mm"
include "ltp1.mm"
include "lelttrd.mm"
include "elrp.mm"
include "sylanbrc.mm"

theorem ge0p1rp
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( A + 1 ) e. RR+ )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    c1
    caddc
    co
    #
    cr
    wcel
    #
    cc0
    @3
    clt
    wbr
    @3
    crp
    wcel
    @0
    @4
    @1
    cA
    peano2re
    adantr
    #
    @2
    cc0
    cA
    @3
    @2
    0red
    @0
    @1
    simpl
    @5
    @0
    @1
    simpr
    @0
    cA
    @3
    clt
    wbr
    @1
    cA
    ltp1
    adantr
    lelttrd
    @3
    elrp
    sylanbrc
end
