include "cn0.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "simpr.mm"
include "cle.mm"
include "simp2.mm"
include "simp1.mm"
include "cr.mm"
include "wi.mm"
include "nn0re.mm"
include "ltle.mm"
include "syl2anr.mm"
include "3impia.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "adantr.mm"
include "ffvelrnd.mm"

theorem fvffz0
  let cP: class P
  let cI: class I
  let cN: class N
  let cV: class V


  assert |- ( ( ( N e. NN0 /\ I e. NN0 /\ I < N ) /\ P : ( 0 ... N ) --> V ) -> ( P ` I ) e. V )

  proof
    cN
    cn0
    wcel
    #
    cI
    cn0
    wcel
    #
    cI
    cN
    clt
    wbr
    #
    w3a
    #
    cc0
    cN
    cfz
    co
    #
    cV
    cP
    wf
    #
    wa
    @4
    cV
    cI
    cP
    @3
    @5
    simpr
    @3
    cI
    @4
    wcel
    #
    @5
    @3
    @1
    @0
    cI
    cN
    cle
    wbr
    #
    @6
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    @7
    @1
    cI
    cr
    wcel
    cN
    cr
    wcel
    @2
    @7
    wi
    @0
    cI
    nn0re
    cN
    nn0re
    cI
    cN
    ltle
    syl2anr
    3impia
    cI
    cN
    elfz2nn0
    syl3anbrc
    adantr
    ffvelrnd
end
