include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdvds.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "absdvdsb.mm"
include "adantlr.mm"
include "cn.mm"
include "nnabscl.mm"
include "dvdsval3.mm"
include "sylan.mm"
include "bitrd.mm"
include "an32s.mm"
include "3impa.mm"

theorem dvdsabsmod0
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ M =/= 0 ) -> ( M || N <-> ( N mod ( abs ` M ) ) = 0 ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cc0
    wne
    #
    cM
    cN
    cdvds
    wbr
    #
    cN
    cM
    cabs
    cfv
    #
    cmo
    co
    cc0
    wceq
    #
    wb
    #
    @0
    @2
    @1
    @6
    @0
    @2
    wa
    #
    @1
    wa
    @3
    @4
    cN
    cdvds
    wbr
    #
    @5
    @0
    @1
    @3
    @8
    wb
    @2
    cM
    cN
    absdvdsb
    adantlr
    @7
    @4
    cn
    wcel
    @1
    @8
    @5
    wb
    cM
    nnabscl
    @4
    cN
    dvdsval3
    sylan
    bitrd
    an32s
    3impa
end
