include "c2.mm"
include "ccht.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clog.mm"
include "df-2.mm"
include "fveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "wceq.mm"
include "1z.mm"
include "2prm.mm"
include "eqeltrri.mm"
include "chtprm.mm"
include "mp2an.mm"
include "cc0.mm"
include "cht1.mm"
include "eqcomi.mm"
include "oveq12i.mm"
include "crp.mm"
include "cr.mm"
include "2rp.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "recni.mm"
include "addid2i.mm"
include "eqtr3i.mm"
include "3eqtri.mm"

theorem cht2



  assert |- ( theta ` 2 ) = ( log ` 2 )

  proof
    c2
    ccht
    cfv
    c1
    c1
    caddc
    co
    #
    ccht
    cfv
    #
    c1
    ccht
    cfv
    #
    @0
    clog
    cfv
    #
    caddc
    co
    #
    c2
    clog
    cfv
    #
    c2
    @0
    ccht
    df-2
    fveq2i
    c1
    cz
    wcel
    @0
    cprime
    wcel
    @1
    @4
    wceq
    1z
    c2
    @0
    cprime
    df-2
    2prm
    eqeltrri
    c1
    chtprm
    mp2an
    cc0
    @5
    caddc
    co
    @4
    @5
    cc0
    @2
    @5
    @3
    caddc
    @2
    cc0
    cht1
    eqcomi
    c2
    @0
    clog
    df-2
    fveq2i
    oveq12i
    @5
    @5
    c2
    crp
    wcel
    @5
    cr
    wcel
    2rp
    c2
    relogcl
    ax-mp
    recni
    addid2i
    eqtr3i
    3eqtri
end
