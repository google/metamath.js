include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cr.mm"
include "crp.mm"
include "wb.mm"
include "zre.mm"
include "nnrp.mm"
include "modid2.mm"
include "syl2an.mm"
include "nnz.mm"
include "w3a.mm"
include "0z.mm"
include "elfzm11.mm"
include "mpan.mm"
include "3anass.mm"
include "syl6bb.mm"
include "syl.mm"
include "ibar.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "bitr4d.mm"

theorem zmodid2
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. NN ) -> ( ( M mod N ) = M <-> M e. ( 0 ... ( N - 1 ) ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    cM
    cN
    cmo
    co
    cM
    wceq
    #
    cc0
    cM
    cle
    wbr
    #
    cM
    cN
    clt
    wbr
    #
    wa
    #
    cM
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    wcel
    #
    @0
    cM
    cr
    wcel
    cN
    crp
    wcel
    @2
    @5
    wb
    @1
    cM
    zre
    cN
    nnrp
    cM
    cN
    modid2
    syl2an
    @1
    @6
    @0
    @5
    wa
    #
    @0
    @5
    @1
    cN
    cz
    wcel
    #
    @6
    @7
    wb
    cN
    nnz
    @8
    @6
    @0
    @3
    @4
    w3a
    #
    @7
    cc0
    cz
    wcel
    @8
    @6
    @9
    wb
    0z
    cM
    cc0
    cN
    elfzm11
    mpan
    @0
    @3
    @4
    3anass
    syl6bb
    syl
    @0
    @5
    @7
    @0
    @5
    ibar
    bicomd
    sylan9bbr
    bitr4d
end
