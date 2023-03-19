include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cfzo.mm"
include "zmodid2.mm"
include "nnz.mm"
include "fzoval.mm"
include "syl.mm"
include "adantl.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "bitrd.mm"

theorem zmodidfzo
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. NN ) -> ( ( M mod N ) = M <-> M e. ( 0 ..^ N ) ) )

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
    #
    cM
    cN
    cmo
    co
    cM
    wceq
    cM
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    cM
    cc0
    cN
    cfzo
    co
    #
    wcel
    cM
    cN
    zmodid2
    @2
    @3
    @4
    cM
    @2
    @4
    @3
    @1
    @4
    @3
    wceq
    #
    @0
    @1
    cN
    cz
    wcel
    @5
    cN
    nnz
    cc0
    cN
    fzoval
    syl
    adantl
    eqcomd
    eleq2d
    bitrd
end
