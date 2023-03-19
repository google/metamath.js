include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cle.mm"
include "wb.mm"
include "peano2zm.mm"
include "zltp1le.mm"
include "sylan.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "adantr.mm"
include "breq1d.mm"
include "bitr2d.mm"

theorem zlem1lt
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M <_ N <-> ( M - 1 ) < N ) )

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
    c1
    cmin
    co
    #
    cN
    clt
    wbr
    #
    @3
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    cM
    cN
    cle
    wbr
    @0
    @3
    cz
    wcel
    @1
    @4
    @6
    wb
    cM
    peano2zm
    @3
    cN
    zltp1le
    sylan
    @2
    @5
    cM
    cN
    cle
    @0
    @5
    cM
    wceq
    #
    @1
    @0
    cM
    cc
    wcel
    c1
    cc
    wcel
    @7
    cM
    zcn
    ax-1cn
    cM
    c1
    npcan
    sylancl
    adantr
    breq1d
    bitr2d
end
