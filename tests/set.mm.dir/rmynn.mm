include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "crmy.mm"
include "co.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "nnz.mm"
include "frmy.mm"
include "fovcl.mm"
include "sylan2.mm"
include "wceq.mm"
include "rmy0.mm"
include "adantr.mm"
include "nngt0.mm"
include "adantl.mm"
include "wb.mm"
include "simpl.mm"
include "0zd.mm"
include "ltrmy.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "elnnz.mm"
include "sylanbrc.mm"

theorem rmynn
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( A rmY N ) e. NN )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    cN
    crmy
    co
    #
    cz
    wcel
    #
    cc0
    @4
    clt
    wbr
    @4
    cn
    wcel
    @2
    @1
    cN
    cz
    wcel
    #
    @5
    cN
    nnz
    #
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    @3
    cA
    cc0
    crmy
    co
    #
    cc0
    @4
    clt
    @1
    @8
    cc0
    wceq
    @2
    cA
    rmy0
    adantr
    @3
    cc0
    cN
    clt
    wbr
    #
    @8
    @4
    clt
    wbr
    #
    @2
    @9
    @1
    cN
    nngt0
    adantl
    @3
    @1
    cc0
    cz
    wcel
    @6
    @9
    @10
    wb
    @1
    @2
    simpl
    @3
    0zd
    @2
    @6
    @1
    @7
    adantl
    cA
    cc0
    cN
    ltrmy
    syl3anc
    mpbid
    eqbrtrrd
    @4
    elnnz
    sylanbrc
end
