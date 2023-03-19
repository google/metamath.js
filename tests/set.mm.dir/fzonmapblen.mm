include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "caddc.mm"
include "cr.mm"
include "wa.mm"
include "wi.mm"
include "cn0.mm"
include "cn.mm"
include "w3a.mm"
include "elfzo0.mm"
include "nn0re.mm"
include "nnre.mm"
include "anim12i.mm"
include "3adant3.mm"
include "sylbi.mm"
include "elfzoelz.mm"
include "zred.mm"
include "simpr.mm"
include "simpll.mm"
include "resubcl.mm"
include "ancoms.mm"
include "adantr.mm"
include "ltadd1d.mm"
include "biimpa.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "pncan3.mm"
include "syl.mm"
include "breqtrd.mm"
include "ex.mm"
include "syl2an.mm"
include "3impia.mm"

theorem fzonmapblen
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. ( 0 ..^ N ) /\ B e. ( 0 ..^ N ) /\ B < A ) -> ( B + ( N - A ) ) < N )

  proof
    cA
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cB
    cA
    clt
    wbr
    #
    cB
    cN
    cA
    cmin
    co
    #
    caddc
    co
    #
    cN
    clt
    wbr
    #
    @1
    cA
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    wa
    #
    cB
    cr
    wcel
    #
    @3
    @6
    wi
    @2
    @1
    cA
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    cA
    cN
    clt
    wbr
    #
    w3a
    @9
    cA
    cN
    elfzo0
    @11
    @12
    @9
    @13
    @11
    @7
    @12
    @8
    cA
    nn0re
    cN
    nnre
    anim12i
    3adant3
    sylbi
    @2
    cB
    cB
    cc0
    cN
    elfzoelz
    zred
    @9
    @10
    wa
    #
    @3
    @6
    @14
    @3
    wa
    #
    @5
    cA
    @4
    caddc
    co
    #
    cN
    clt
    @14
    @3
    @5
    @16
    clt
    wbr
    @14
    cB
    cA
    @4
    @9
    @10
    simpr
    @7
    @8
    @10
    simpll
    @9
    @4
    cr
    wcel
    #
    @10
    @8
    @7
    @17
    cN
    cA
    resubcl
    ancoms
    adantr
    ltadd1d
    biimpa
    @15
    cA
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    wa
    #
    @16
    cN
    wceq
    @14
    @20
    @3
    @9
    @20
    @10
    @7
    @18
    @8
    @19
    cA
    recn
    cN
    recn
    anim12i
    adantr
    adantr
    cA
    cN
    pncan3
    syl
    breqtrd
    ex
    syl2an
    3impia
end
