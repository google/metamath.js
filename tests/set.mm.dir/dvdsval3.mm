include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "wne.mm"
include "wb.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "dvdsval2.mm"
include "3expa.mm"
include "sylan.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "mod0.mm"
include "syl2anr.mm"
include "bitr4d.mm"

theorem dvdsval3
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. ZZ ) -> ( M || N <-> ( N mod M ) = 0 ) )

  proof
    cM
    cn
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cM
    cN
    cdvds
    wbr
    #
    cN
    cM
    cdiv
    co
    cz
    wcel
    #
    cN
    cM
    cmo
    co
    cc0
    wceq
    #
    @0
    cM
    cz
    wcel
    #
    cM
    cc0
    wne
    #
    wa
    @1
    @2
    @3
    wb
    #
    @0
    @5
    @6
    cM
    nnz
    cM
    nnne0
    jca
    @5
    @6
    @1
    @7
    cM
    cN
    dvdsval2
    3expa
    sylan
    @1
    cN
    cr
    wcel
    cM
    crp
    wcel
    @4
    @3
    wb
    @0
    cN
    zre
    cM
    nnrp
    cN
    cM
    mod0
    syl2anr
    bitr4d
end
