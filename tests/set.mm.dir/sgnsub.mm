include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "csgn.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "simpll.mm"
include "rexrd.mm"
include "eqeq2.mm"
include "simpr.mm"
include "cc.mm"
include "recnd.mm"
include "adantr.mm"
include "simplr.mm"
include "lt0ne0d.mm"
include "mulne0bad.mm"
include "pm2.21ddne.mm"
include "cxr.mm"
include "simplll.mm"
include "simpllr.mm"
include "resubcld.mm"
include "0red.mm"
include "mul2lt0lgt0.mm"
include "lttrd.mm"
include "simpl.mm"
include "posdifd.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "sgnp.mm"
include "syl2anc.mm"
include "subid1d.mm"
include "mul2lt0llt0.mm"
include "eqbrtrd.mm"
include "ltsub23d.mm"
include "sgnn.mm"
include "sgn3da.mm"

theorem sgnsub
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( A x. B ) < 0 ) -> ( sgn ` ( A - B ) ) = ( sgn ` A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wa
    #
    cA
    cB
    cmin
    co
    #
    csgn
    cfv
    #
    cA
    csgn
    cfv
    #
    wceq
    @7
    cc0
    wceq
    #
    @7
    c1
    wceq
    #
    @7
    c1
    cneg
    #
    wceq
    #
    cA
    @5
    cA
    @0
    @1
    @4
    simpll
    #
    rexrd
    @8
    cc0
    @7
    eqeq2
    @8
    c1
    @7
    eqeq2
    @8
    @11
    @7
    eqeq2
    @5
    cA
    cc0
    wceq
    #
    wa
    #
    @9
    cA
    cc0
    @5
    @14
    simpr
    @15
    cA
    cB
    @5
    cA
    cc
    wcel
    #
    @14
    @5
    cA
    @13
    recnd
    #
    adantr
    @5
    cB
    cc
    wcel
    @14
    @5
    cB
    @0
    @1
    @4
    simplr
    #
    recnd
    adantr
    @15
    @3
    @2
    @4
    @14
    simplr
    lt0ne0d
    mulne0bad
    pm2.21ddne
    @5
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @6
    cxr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    @10
    @20
    @6
    @20
    cA
    cB
    @0
    @1
    @4
    @19
    simplll
    #
    @0
    @1
    @4
    @19
    simpllr
    #
    resubcld
    rexrd
    @20
    @0
    @1
    cB
    cA
    clt
    wbr
    #
    @22
    @23
    @24
    @20
    cB
    cc0
    cA
    @24
    @20
    0red
    @23
    @5
    cA
    cB
    @13
    @18
    @2
    @4
    simpr
    #
    mul2lt0lgt0
    @5
    @19
    simpr
    lttrd
    @2
    @25
    @22
    @2
    cB
    cA
    @0
    @1
    simpr
    @0
    @1
    simpl
    posdifd
    biimpa
    syl21anc
    @6
    sgnp
    syl2anc
    @5
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    @21
    @6
    cc0
    clt
    wbr
    @12
    @28
    @6
    @28
    cA
    cB
    @0
    @1
    @4
    @27
    simplll
    #
    @0
    @1
    @4
    @27
    simpllr
    #
    resubcld
    rexrd
    @28
    cA
    cc0
    cB
    @29
    @28
    0red
    #
    @30
    @28
    cA
    cc0
    cmin
    co
    cA
    cB
    clt
    @28
    cA
    @5
    @16
    @27
    @17
    adantr
    subid1d
    @28
    cA
    cc0
    cB
    @29
    @31
    @30
    @5
    @27
    simpr
    @5
    cA
    cB
    @13
    @18
    @26
    mul2lt0llt0
    lttrd
    eqbrtrd
    ltsub23d
    @6
    sgnn
    syl2anc
    sgn3da
end
