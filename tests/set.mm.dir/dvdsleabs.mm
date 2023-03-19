include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wb.mm"
include "dvdsabsb.mm"
include "3adant3.mm"
include "wi.mm"
include "wa.mm"
include "cn.mm"
include "nnabscl.mm"
include "dvdsle.mm"
include "sylan2.mm"
include "3impb.mm"
include "sylbid.mm"

theorem dvdsleabs
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> ( M || N -> M <_ ( abs ` N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    w3a
    cM
    cN
    cdvds
    wbr
    #
    cM
    cN
    cabs
    cfv
    #
    cdvds
    wbr
    #
    cM
    @4
    cle
    wbr
    #
    @0
    @1
    @3
    @5
    wb
    @2
    cM
    cN
    dvdsabsb
    3adant3
    @0
    @1
    @2
    @5
    @6
    wi
    #
    @1
    @2
    wa
    @0
    @4
    cn
    wcel
    @7
    cN
    nnabscl
    cM
    @4
    dvdsle
    sylan2
    3impb
    sylbid
end
