include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "cz.mm"
include "wi.mm"
include "prmz.mm"
include "adantl.mm"
include "zsqcl.mm"
include "syl.mm"
include "nnz.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "dvdsmultr1.mm"
include "syl3anc.mm"
include "reximdva.mm"
include "wb.mm"
include "isnsqf.mm"
include "adantr.mm"
include "nnmulcl.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem mumullem1
  let cA: class A
  let cB: class B
  let vp: setvar p


  assert |- ( ( ( A e. NN /\ B e. NN ) /\ ( mmu ` A ) = 0 ) -> ( mmu ` ( A x. B ) ) = 0 )

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
    cmu
    cfv
    cc0
    wceq
    #
    cA
    cB
    cmul
    co
    #
    cmu
    cfv
    cc0
    wceq
    #
    @2
    vp
    cv
    #
    c2
    cexp
    co
    #
    cA
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @7
    @4
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @3
    @5
    @2
    @8
    @10
    vp
    cprime
    @2
    @6
    cprime
    wcel
    #
    wa
    #
    @7
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @8
    @10
    wi
    @13
    @6
    cz
    wcel
    #
    @14
    @12
    @17
    @2
    @6
    prmz
    adantl
    @6
    zsqcl
    syl
    @0
    @15
    @1
    @12
    cA
    nnz
    ad2antrr
    @1
    @16
    @0
    @12
    cB
    nnz
    ad2antlr
    @7
    cA
    cB
    dvdsmultr1
    syl3anc
    reximdva
    @0
    @3
    @9
    wb
    @1
    cA
    vp
    isnsqf
    adantr
    @2
    @4
    cn
    wcel
    @5
    @11
    wb
    cA
    cB
    nnmulcl
    @4
    vp
    isnsqf
    syl
    3imtr4d
    imp
end
