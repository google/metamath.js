include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "c7.mm"
include "c6.mm"
include "cmin.mm"
include "co.mm"
include "7re.mm"
include "recni.mm"
include "6re.mm"
include "ax-1cn.mm"
include "caddc.mm"
include "df-7.mm"
include "eqcomi.mm"
include "subaddrii.mm"
include "c3.mm"
include "cmul.mm"
include "3cn.mm"
include "2cn.mm"
include "df-3.mm"
include "oveq1i.mm"
include "mulid2i.mm"
include "eqtri.mm"
include "subdiri.mm"
include "cc.mm"
include "wcel.mm"
include "mulcli.mm"
include "subadd23.mm"
include "mp3an.mm"
include "3t2e6.mm"
include "mulcomi.mm"
include "oveq12i.mm"
include "subcli.mm"
include "oveq2i.mm"
include "subadd2i.mm"
include "biimpri.mm"
include "ax-mp.mm"
include "pm3.2i.mm"

theorem problem4
  let cA: class A
  let cB: class B
  assume problem4.1: |- A e. CC
  assume problem4.2: |- B e. CC
  assume problem4.3: |- ( A + B ) = 3
  assume problem4.4: |- ( ( 3 x. A ) + ( 2 x. B ) ) = 7


  assert |- ( A = 1 /\ B = 2 )

  proof
    cA
    c1
    wceq
    cB
    c2
    wceq
    c1
    cA
    c1
    c7
    c6
    cmin
    co
    #
    cA
    @0
    c1
    c7
    c6
    c1
    c7
    7re
    recni
    #
    c6
    6re
    recni
    #
    ax-1cn
    c7
    c6
    c1
    caddc
    co
    df-7
    eqcomi
    subaddrii
    eqcomi
    cA
    c6
    caddc
    co
    #
    c7
    wceq
    #
    @0
    cA
    wceq
    #
    @3
    c3
    cA
    cmul
    co
    #
    c2
    cB
    cmul
    co
    #
    caddc
    co
    #
    c7
    @3
    @6
    c2
    cA
    cmul
    co
    #
    cmin
    co
    #
    c6
    caddc
    co
    #
    @8
    cA
    @10
    c6
    caddc
    cA
    c3
    c2
    cmin
    co
    #
    cA
    cmul
    co
    #
    @10
    @13
    cA
    @13
    c1
    cA
    cmul
    co
    cA
    @12
    c1
    cA
    cmul
    c3
    c2
    c1
    3cn
    2cn
    ax-1cn
    c3
    c2
    c1
    caddc
    co
    #
    df-3
    eqcomi
    #
    subaddrii
    oveq1i
    cA
    problem4.1
    mulid2i
    eqtri
    eqcomi
    c3
    c2
    cA
    3cn
    2cn
    problem4.1
    subdiri
    eqtri
    oveq1i
    @11
    @6
    c6
    @9
    cmin
    co
    #
    caddc
    co
    #
    @8
    @6
    cc
    wcel
    @9
    cc
    wcel
    c6
    cc
    wcel
    @11
    @17
    wceq
    c3
    cA
    3cn
    problem4.1
    mulcli
    c2
    cA
    2cn
    problem4.1
    mulcli
    @2
    @6
    @9
    c6
    subadd23
    mp3an
    @8
    @17
    @7
    @16
    @6
    caddc
    @16
    @7
    @16
    c3
    c2
    cmul
    co
    #
    cA
    c2
    cmul
    co
    #
    cmin
    co
    #
    @7
    @20
    @16
    @18
    c6
    @19
    @9
    cmin
    3t2e6
    cA
    c2
    problem4.1
    2cn
    mulcomi
    oveq12i
    eqcomi
    @20
    c3
    cA
    cmin
    co
    #
    c2
    cmul
    co
    #
    @7
    @22
    @20
    c3
    cA
    c2
    3cn
    problem4.1
    2cn
    subdiri
    eqcomi
    @22
    c2
    @21
    cmul
    co
    #
    @7
    @23
    @22
    c2
    @21
    2cn
    c3
    cA
    3cn
    problem4.1
    subcli
    mulcomi
    eqcomi
    @7
    @23
    cB
    @21
    c2
    cmul
    @21
    cB
    c3
    cA
    cB
    3cn
    problem4.1
    problem4.2
    problem4.3
    subaddrii
    eqcomi
    #
    oveq2i
    eqcomi
    eqtri
    eqtri
    eqtri
    eqcomi
    oveq2i
    eqcomi
    eqtri
    eqtri
    problem4.4
    eqtri
    @5
    @4
    c7
    c6
    cA
    @1
    @2
    problem4.1
    subadd2i
    biimpri
    ax-mp
    eqtri
    eqcomi
    #
    cB
    @21
    c2
    @24
    @21
    c3
    c1
    cmin
    co
    #
    c2
    cA
    c1
    c3
    cmin
    @25
    oveq2i
    @14
    c3
    wceq
    #
    @26
    c2
    wceq
    #
    @15
    @28
    @27
    c3
    c1
    c2
    3cn
    ax-1cn
    2cn
    subadd2i
    biimpri
    ax-mp
    eqtri
    eqtri
    pm3.2i
end
