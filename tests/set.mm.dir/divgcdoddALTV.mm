include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "cz.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "codd.mm"
include "divgcdodd.mm"
include "nnz.mm"
include "gcddvds.mm"
include "syl2an.mm"
include "simpld.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "wceq.mm"
include "anim12i.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnanrd.mm"
include "adantr.mm"
include "gcdn0cl.mm"
include "syl2anc.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "biantrurd.mm"
include "simprd.mm"
include "adantl.mm"
include "orbi12d.mm"
include "isodd3.mm"
include "orbi12i.mm"
include "sylibr.mm"

theorem divgcdoddALTV
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. NN /\ B e. NN ) -> ( ( A / ( A gcd B ) ) e. Odd \/ ( B / ( A gcd B ) ) e. Odd ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    #
    cz
    wcel
    #
    c2
    @4
    cdvds
    wbr
    wn
    #
    wa
    #
    cB
    @3
    cdiv
    co
    #
    cz
    wcel
    #
    c2
    @8
    cdvds
    wbr
    wn
    #
    wa
    #
    wo
    #
    @4
    codd
    wcel
    #
    @8
    codd
    wcel
    #
    wo
    @2
    @6
    @10
    wo
    @12
    cA
    cB
    divgcdodd
    @2
    @6
    @7
    @10
    @11
    @2
    @5
    @6
    @2
    @3
    cA
    cdvds
    wbr
    #
    @5
    @2
    @15
    @3
    cB
    cdvds
    wbr
    #
    @0
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @15
    @16
    wa
    @1
    cA
    nnz
    #
    cB
    nnz
    #
    cA
    cB
    gcddvds
    syl2an
    #
    simpld
    @2
    @3
    cz
    wcel
    #
    @3
    cc0
    wne
    #
    @17
    @15
    @5
    wb
    @2
    @3
    @2
    @17
    @18
    wa
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    wn
    #
    @3
    cn
    wcel
    @0
    @17
    @1
    @18
    @19
    @20
    anim12i
    @0
    @26
    @1
    @0
    @24
    @25
    @0
    cA
    cc0
    cA
    nnne0
    neneqd
    intnanrd
    adantr
    cA
    cB
    gcdn0cl
    syl2anc
    #
    nnzd
    #
    @2
    @3
    @27
    nnne0d
    #
    @0
    @17
    @1
    @19
    adantr
    @3
    cA
    dvdsval2
    syl3anc
    mpbid
    biantrurd
    @2
    @9
    @10
    @2
    @16
    @9
    @2
    @15
    @16
    @21
    simprd
    @2
    @22
    @23
    @18
    @16
    @9
    wb
    @28
    @29
    @1
    @18
    @0
    @20
    adantl
    @3
    cB
    dvdsval2
    syl3anc
    mpbid
    biantrurd
    orbi12d
    mpbid
    @13
    @7
    @14
    @11
    @4
    isodd3
    @8
    isodd3
    orbi12i
    sylibr
end
