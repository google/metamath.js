include "c3.mm"
include "ccht.mm"
include "cfv.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clog.mm"
include "c6.mm"
include "df-3.mm"
include "fveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "wceq.mm"
include "2z.mm"
include "3prm.mm"
include "eqeltrri.mm"
include "chtprm.mm"
include "mp2an.mm"
include "cmul.mm"
include "crp.mm"
include "2rp.mm"
include "3re.mm"
include "3pos.mm"
include "elrpii.mm"
include "relogmul.mm"
include "3cn.mm"
include "2cn.mm"
include "3t2e6.mm"
include "mulcomli.mm"
include "cht2.mm"
include "eqcomi.mm"
include "oveq12i.mm"
include "3eqtr3ri.mm"
include "3eqtri.mm"

theorem cht3



  assert |- ( theta ` 3 ) = ( log ` 6 )

  proof
    c3
    ccht
    cfv
    c2
    c1
    caddc
    co
    #
    ccht
    cfv
    #
    c2
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
    c6
    clog
    cfv
    #
    c3
    @0
    ccht
    df-3
    fveq2i
    c2
    cz
    wcel
    @0
    cprime
    wcel
    @1
    @4
    wceq
    2z
    c3
    @0
    cprime
    df-3
    3prm
    eqeltrri
    c2
    chtprm
    mp2an
    c2
    c3
    cmul
    co
    #
    clog
    cfv
    #
    c2
    clog
    cfv
    #
    c3
    clog
    cfv
    #
    caddc
    co
    #
    @5
    @4
    c2
    crp
    wcel
    c3
    crp
    wcel
    @7
    @10
    wceq
    2rp
    c3
    3re
    3pos
    elrpii
    c2
    c3
    relogmul
    mp2an
    @6
    c6
    clog
    c3
    c2
    c6
    3cn
    2cn
    3t2e6
    mulcomli
    fveq2i
    @8
    @2
    @9
    @3
    caddc
    @2
    @8
    cht2
    eqcomi
    c3
    @0
    clog
    df-3
    fveq2i
    oveq12i
    3eqtr3ri
    3eqtri
end
