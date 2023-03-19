include "c3.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cneg.mm"
include "wa.mm"
include "cceil.mm"
include "ex-fl.mm"
include "cr.mm"
include "wcel.mm"
include "3re.mm"
include "rehalfcli.mm"
include "renegcli.mm"
include "ceilval.mm"
include "ax-mp.mm"
include "recni.mm"
include "negnegi.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "negeqd.mm"
include "syl5eq.mm"
include "negeq.mm"
include "2cn.mm"
include "syl6eq.mm"
include "anim12ci.mm"

theorem ex-ceil



  assert |- ( ( |^ ` ( 3 / 2 ) ) = 2 /\ ( |^ ` -u ( 3 / 2 ) ) = -u 1 )

  proof
    c3
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    wceq
    #
    @0
    cneg
    #
    cfl
    cfv
    #
    c2
    cneg
    #
    wceq
    #
    wa
    @0
    cceil
    cfv
    #
    c2
    wceq
    #
    @3
    cceil
    cfv
    #
    c1
    cneg
    #
    wceq
    #
    wa
    ex-fl
    @2
    @11
    @6
    @8
    @2
    @9
    @3
    cneg
    #
    cfl
    cfv
    #
    cneg
    #
    @10
    @3
    cr
    wcel
    @9
    @14
    wceq
    @0
    c3
    3re
    rehalfcli
    #
    renegcli
    @3
    ceilval
    ax-mp
    @2
    @13
    c1
    @2
    @13
    c1
    wceq
    @1
    @13
    c1
    @0
    @12
    cfl
    @12
    @0
    @0
    @0
    @15
    recni
    negnegi
    eqcomi
    fveq2i
    eqeq1i
    biimpi
    negeqd
    syl5eq
    @6
    @7
    @4
    cneg
    #
    c2
    @0
    cr
    wcel
    @7
    @16
    wceq
    @15
    @0
    ceilval
    ax-mp
    @6
    @16
    @5
    cneg
    c2
    @4
    @5
    negeq
    c2
    2cn
    negnegi
    syl6eq
    syl5eq
    anim12ci
    ax-mp
end
