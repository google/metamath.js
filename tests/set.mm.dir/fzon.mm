include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cfz.mm"
include "c0.mm"
include "wceq.mm"
include "cle.mm"
include "cfzo.mm"
include "wb.mm"
include "peano2zm.mm"
include "fzn.mm"
include "sylan2.mm"
include "zlem1lt.mm"
include "ancoms.mm"
include "fzoval.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "3bitr4d.mm"

theorem fzon
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( N <_ M <-> ( M ..^ N ) = (/) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    c1
    cmin
    co
    #
    cM
    clt
    wbr
    #
    cM
    @3
    cfz
    co
    #
    c0
    wceq
    #
    cN
    cM
    cle
    wbr
    #
    cM
    cN
    cfzo
    co
    #
    c0
    wceq
    @1
    @0
    @3
    cz
    wcel
    @4
    @6
    wb
    cN
    peano2zm
    cM
    @3
    fzn
    sylan2
    @1
    @0
    @7
    @4
    wb
    cN
    cM
    zlem1lt
    ancoms
    @2
    @8
    @5
    c0
    @1
    @8
    @5
    wceq
    @0
    cM
    cN
    fzoval
    adantl
    eqeq1d
    3bitr4d
end
