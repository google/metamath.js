include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "clt.mm"
include "wb.mm"
include "peano2zm.mm"
include "zleltp1.mm"
include "sylan2.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "adantl.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem zltlem1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M < N <-> M <_ ( N - 1 ) ) )

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
    cM
    cN
    c1
    cmin
    co
    #
    cle
    wbr
    #
    cM
    @3
    c1
    caddc
    co
    #
    clt
    wbr
    #
    cM
    cN
    clt
    wbr
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
    zleltp1
    sylan2
    @2
    @5
    cN
    cM
    clt
    @1
    @5
    cN
    wceq
    #
    @0
    @1
    cN
    cc
    wcel
    c1
    cc
    wcel
    @7
    cN
    zcn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    adantl
    breq2d
    bitr2d
end
