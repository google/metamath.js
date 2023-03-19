include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wn.mm"
include "wa.mm"
include "cneg.mm"
include "cn.mm"
include "wo.mm"
include "cr.mm"
include "simpl.mm"
include "znegcld.mm"
include "elznn.mm"
include "sylib.mm"
include "simprd.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "negnegd.mm"
include "simpr.mm"
include "eqneltrd.mm"
include "wi.mm"
include "ax-1.mm"
include "pm2.24.mm"
include "jaoi.mm"
include "sylc.mm"

theorem znnn0nn
  let cN: class N


  assert |- ( ( N e. ZZ /\ -. N e. NN0 ) -> -u N e. NN )

  proof
    cN
    cz
    wcel
    #
    cN
    cn0
    wcel
    wn
    #
    wa
    #
    cN
    cneg
    #
    cn
    wcel
    #
    @3
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    @6
    wn
    #
    @4
    @2
    @3
    cr
    wcel
    #
    @7
    @2
    @3
    cz
    wcel
    @9
    @7
    wa
    @2
    cN
    @0
    @1
    simpl
    znegcld
    @3
    elznn
    sylib
    simprd
    @2
    @5
    cN
    cn0
    @2
    cN
    @0
    cN
    cc
    wcel
    @1
    cN
    zcn
    adantr
    negnegd
    @0
    @1
    simpr
    eqneltrd
    @4
    @8
    @4
    wi
    @6
    @4
    @8
    ax-1
    @6
    @4
    pm2.24
    jaoi
    sylc
end
