include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "nnz.mm"
include "anim1i.mm"
include "gcddvds.mm"
include "simpld.mm"
include "syl.mm"
include "wb.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "adantr.mm"
include "intnanrd.mm"
include "gcdn0cl.mm"
include "syl2anc.mm"
include "nndivdvds.mm"
include "syldan.mm"
include "mpbid.mm"

theorem divgcdnn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. ZZ ) -> ( A / ( A gcd B ) ) e. NN )

  proof
    cA
    cn
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cgcd
    co
    #
    cA
    cdvds
    wbr
    #
    cA
    @3
    cdiv
    co
    cn
    wcel
    #
    @2
    cA
    cz
    wcel
    #
    @1
    wa
    #
    @4
    @0
    @6
    @1
    cA
    nnz
    anim1i
    #
    @7
    @4
    @3
    cB
    cdvds
    wbr
    cA
    cB
    gcddvds
    simpld
    syl
    @0
    @1
    @3
    cn
    wcel
    #
    @4
    @5
    wb
    @2
    @7
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
    @9
    @8
    @2
    @10
    @11
    @0
    @10
    wn
    @1
    @0
    cA
    cc0
    cA
    nnne0
    neneqd
    adantr
    intnanrd
    cA
    cB
    gcdn0cl
    syl2anc
    cA
    @3
    nndivdvds
    syldan
    mpbid
end
