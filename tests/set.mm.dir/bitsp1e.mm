include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cbits.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfl.mm"
include "wb.mm"
include "2z.mm"
include "a1i.mm"
include "id.mm"
include "zmulcld.mm"
include "bitsp1.mm"
include "sylan.mm"
include "wceq.mm"
include "zcn.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "fveq2d.mm"
include "flid.mm"
include "eqtrd.mm"
include "adantr.mm"
include "eleq2d.mm"
include "bitrd.mm"

theorem bitsp1e
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> ( ( M + 1 ) e. ( bits ` ( 2 x. N ) ) <-> M e. ( bits ` N ) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    cM
    c1
    caddc
    co
    c2
    cN
    cmul
    co
    #
    cbits
    cfv
    wcel
    #
    cM
    @3
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cbits
    cfv
    #
    wcel
    #
    cM
    cN
    cbits
    cfv
    #
    wcel
    @0
    @3
    cz
    wcel
    @1
    @4
    @8
    wb
    @0
    c2
    cN
    c2
    cz
    wcel
    @0
    2z
    a1i
    @0
    id
    zmulcld
    cM
    @3
    bitsp1
    sylan
    @2
    @7
    @9
    cM
    @2
    @6
    cN
    cbits
    @0
    @6
    cN
    wceq
    @1
    @0
    @6
    cN
    cfl
    cfv
    cN
    @0
    @5
    cN
    cfl
    @0
    cN
    c2
    cN
    zcn
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan3d
    fveq2d
    cN
    flid
    eqtrd
    adantr
    fveq2d
    eleq2d
    bitrd
end
