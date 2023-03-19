include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "elnn0.mm"
include "elnnz.mm"
include "eqcom.mm"
include "orbi12i.mm"
include "id.mm"
include "0z.mm"
include "eleq1.mm"
include "mpbii.mm"
include "jaoi.mm"
include "orc.mm"
include "impbii.mm"
include "anbi1i.mm"
include "ordir.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "zre.mm"
include "leloe.mm"
include "sylancr.mm"
include "pm5.32i.mm"
include "3bitr4i.mm"
include "3bitri.mm"

theorem elnn0z
  let cN: class N


  assert |- ( N e. NN0 <-> ( N e. ZZ /\ 0 <_ N ) )

  proof
    cN
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cN
    cz
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    wa
    #
    cc0
    cN
    wceq
    #
    wo
    #
    @2
    cc0
    cN
    cle
    wbr
    #
    wa
    #
    cN
    elnn0
    @0
    @4
    @1
    @5
    cN
    elnnz
    cN
    cc0
    eqcom
    orbi12i
    @2
    @5
    wo
    #
    @3
    @5
    wo
    #
    wa
    @2
    @10
    wa
    @6
    @8
    @9
    @2
    @10
    @9
    @2
    @2
    @2
    @5
    @2
    id
    @5
    cc0
    cz
    wcel
    @2
    0z
    cc0
    cN
    cz
    eleq1
    mpbii
    jaoi
    @2
    @5
    orc
    impbii
    anbi1i
    @2
    @3
    @5
    ordir
    @2
    @7
    @10
    @2
    cc0
    cr
    wcel
    cN
    cr
    wcel
    @7
    @10
    wb
    0re
    cN
    zre
    cc0
    cN
    leloe
    sylancr
    pm5.32i
    3bitr4i
    3bitri
end
