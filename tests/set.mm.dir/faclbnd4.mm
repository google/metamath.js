include "cn0.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "caddc.mm"
include "cfa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "elnn0.mm"
include "faclbnd4lem4.mm"
include "3com13.mm"
include "3expa.mm"
include "faclbnd4lem3.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "3impa.mm"

theorem faclbnd4
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( N e. NN0 /\ K e. NN0 /\ M e. NN0 ) -> ( ( N ^ K ) x. ( M ^ N ) ) <_ ( ( ( 2 ^ ( K ^ 2 ) ) x. ( M ^ ( M + K ) ) ) x. ( ! ` N ) ) )

  proof
    cM
    cn0
    wcel
    #
    cK
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cK
    cexp
    co
    cM
    cN
    cexp
    co
    cmul
    co
    c2
    cK
    c2
    cexp
    co
    cexp
    co
    cM
    cM
    cK
    caddc
    co
    cexp
    co
    cmul
    co
    cN
    cfa
    cfv
    cmul
    co
    cle
    wbr
    #
    @0
    @1
    @2
    @3
    @2
    @0
    @1
    wa
    #
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @3
    cN
    elnn0
    @4
    @5
    @3
    @6
    @0
    @1
    @5
    @3
    @5
    @1
    @0
    @3
    cK
    cM
    cN
    faclbnd4lem4
    3com13
    3expa
    cK
    cM
    cN
    faclbnd4lem3
    jaodan
    sylan2b
    3impa
    3com13
end
