include "c1.mm"
include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "wo.mm"
include "cn0.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "simpl.mm"
include "cr.mm"
include "w3a.mm"
include "clt.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "nn0re.mm"
include "3jca.mm"
include "adantr.mm"
include "simpr.mm"
include "1lt2.mm"
include "jctil.mm"
include "ltleletr.mm"
include "sylc.mm"
include "elnnnn0c.mm"
include "sylanbrc.mm"
include "nn1m1nn.mm"
include "syl.mm"
include "wi.mm"
include "breq2.mm"
include "wn.mm"
include "1re.mm"
include "ltnlei.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "adantld.mm"
include "ax-1.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem nn0ge2m1nn
  let cN: class N


  assert |- ( ( N e. NN0 /\ 2 <_ N ) -> ( N - 1 ) e. NN )

  proof
    cN
    c1
    wceq
    #
    cN
    c1
    cmin
    co
    cn
    wcel
    #
    wo
    #
    cN
    cn0
    wcel
    #
    c2
    cN
    cle
    wbr
    #
    wa
    #
    @1
    @5
    cN
    cn
    wcel
    #
    @2
    @5
    @3
    c1
    cN
    cle
    wbr
    #
    @6
    @3
    @4
    simpl
    @5
    c1
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    c1
    c2
    clt
    wbr
    #
    @4
    wa
    @7
    @3
    @11
    @4
    @3
    @8
    @9
    @10
    @3
    1red
    @9
    @3
    2re
    a1i
    cN
    nn0re
    3jca
    adantr
    @5
    @4
    @12
    @3
    @4
    simpr
    1lt2
    jctil
    c1
    c2
    cN
    ltleletr
    sylc
    cN
    elnnnn0c
    sylanbrc
    cN
    nn1m1nn
    syl
    @0
    @5
    @1
    wi
    @1
    @0
    @4
    @1
    @3
    @0
    @4
    c2
    c1
    cle
    wbr
    #
    @1
    cN
    c1
    c2
    cle
    breq2
    @12
    @13
    @1
    wi
    #
    1lt2
    @12
    @13
    wn
    @14
    c1
    c2
    1re
    2re
    ltnlei
    @13
    @1
    pm2.21
    sylbi
    ax-mp
    syl6bi
    adantld
    @1
    @5
    ax-1
    jaoi
    mpcom
end
