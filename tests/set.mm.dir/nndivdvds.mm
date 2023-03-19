include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "cz.mm"
include "wne.mm"
include "wb.mm"
include "nnz.mm"
include "adantl.mm"
include "nnne0.mm"
include "adantr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "anbi1d.mm"
include "cr.mm"
include "nnre.mm"
include "nngt0.mm"
include "divgt0d.mm"
include "biantrud.mm"
include "elnnz.mm"
include "a1i.mm"
include "3bitr4d.mm"

theorem nndivdvds
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. NN ) -> ( B || A <-> ( A / B ) e. NN ) )

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
    cB
    cA
    cdvds
    wbr
    #
    cc0
    cA
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    wa
    @4
    cz
    wcel
    #
    @5
    wa
    #
    @3
    @4
    cn
    wcel
    #
    @2
    @3
    @6
    @5
    @2
    cB
    cz
    wcel
    #
    cB
    cc0
    wne
    #
    cA
    cz
    wcel
    #
    @3
    @6
    wb
    @1
    @9
    @0
    cB
    nnz
    adantl
    @1
    @10
    @0
    cB
    nnne0
    adantl
    @0
    @11
    @1
    cA
    nnz
    adantr
    cB
    cA
    dvdsval2
    syl3anc
    anbi1d
    @2
    @5
    @3
    @2
    cA
    cB
    @0
    cA
    cr
    wcel
    @1
    cA
    nnre
    adantr
    @1
    cB
    cr
    wcel
    @0
    cB
    nnre
    adantl
    @0
    cc0
    cA
    clt
    wbr
    @1
    cA
    nngt0
    adantr
    @1
    cc0
    cB
    clt
    wbr
    @0
    cB
    nngt0
    adantl
    divgt0d
    biantrud
    @8
    @7
    wb
    @2
    @4
    elnnz
    a1i
    3bitr4d
end
