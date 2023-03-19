include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "cc.mm"
include "eluzelcn.mm"
include "adantl.mm"
include "zcn.mm"
include "adantr.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "crp.mm"
include "wceq.mm"
include "eluz2nn.mm"
include "nnrpd.mm"
include "mulmod0.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "cr.mm"
include "eluzelre.mm"
include "zre.mm"
include "remulcld.mm"
include "1red.mm"
include "modaddmod.mm"
include "syl3anc.mm"
include "clt.mm"
include "wbr.mm"
include "eluz2gt1.mm"
include "jca.mm"
include "1mod.mm"
include "syl.mm"
include "3eqtr3d.mm"

theorem mulp1mod1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ZZ /\ N e. ( ZZ>= ` 2 ) ) -> ( ( ( N x. A ) + 1 ) mod N ) = 1 )

  proof
    cA
    cz
    wcel
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wa
    #
    cN
    cA
    cmul
    co
    #
    cN
    cmo
    co
    #
    c1
    caddc
    co
    #
    cN
    cmo
    co
    #
    c1
    cN
    cmo
    co
    #
    @3
    c1
    caddc
    co
    cN
    cmo
    co
    #
    c1
    @2
    @5
    c1
    cN
    cmo
    @2
    @5
    cc0
    c1
    caddc
    co
    c1
    @2
    @4
    cc0
    c1
    caddc
    @2
    @4
    cA
    cN
    cmul
    co
    #
    cN
    cmo
    co
    #
    cc0
    @2
    @3
    @9
    cN
    cmo
    @2
    cN
    cA
    @1
    cN
    cc
    wcel
    @0
    c2
    cN
    eluzelcn
    adantl
    @0
    cA
    cc
    wcel
    @1
    cA
    zcn
    adantr
    mulcomd
    oveq1d
    @1
    @0
    cN
    crp
    wcel
    #
    @10
    cc0
    wceq
    @1
    cN
    cN
    eluz2nn
    nnrpd
    #
    cA
    cN
    mulmod0
    sylan2
    eqtrd
    oveq1d
    0p1e1
    syl6eq
    oveq1d
    @2
    @3
    cr
    wcel
    c1
    cr
    wcel
    @11
    @6
    @8
    wceq
    @2
    cN
    cA
    @1
    cN
    cr
    wcel
    #
    @0
    c2
    cN
    eluzelre
    #
    adantl
    @0
    cA
    cr
    wcel
    @1
    cA
    zre
    adantr
    remulcld
    @2
    1red
    @1
    @11
    @0
    @12
    adantl
    @3
    c1
    cN
    modaddmod
    syl3anc
    @2
    @13
    c1
    cN
    clt
    wbr
    #
    wa
    #
    @7
    c1
    wceq
    @1
    @16
    @0
    @1
    @13
    @15
    @14
    cN
    eluz2gt1
    jca
    adantl
    cN
    1mod
    syl
    3eqtr3d
end
