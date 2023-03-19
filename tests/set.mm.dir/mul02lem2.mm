include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "ax-1ne0.mm"
include "wa.mm"
include "caddc.mm"
include "ci.mm"
include "cc.mm"
include "ax-1cn.mm"
include "mul02lem1.mm"
include "mpan2.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "ax-icn.mm"
include "mulcli.mm"
include "addassi.mm"
include "ax-i2m1.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "00id.mm"
include "eqtr4i.mm"
include "3eqtr3g.mm"
include "wb.mm"
include "1re.mm"
include "0re.mm"
include "readdcan.mm"
include "mp3an.mm"
include "sylib.mm"
include "ex.mm"
include "necon1d.mm"
include "mpi.mm"

theorem mul02lem2
  let cA: class A


  assert |- ( A e. RR -> ( 0 x. A ) = 0 )

  proof
    cA
    cr
    wcel
    #
    c1
    cc0
    wne
    cc0
    cA
    cmul
    co
    #
    cc0
    wceq
    ax-1ne0
    @0
    @1
    cc0
    c1
    cc0
    @0
    @1
    cc0
    wne
    #
    c1
    cc0
    wceq
    #
    @0
    @2
    wa
    #
    cc0
    c1
    caddc
    co
    #
    cc0
    cc0
    caddc
    co
    #
    wceq
    #
    @3
    @4
    ci
    ci
    cmul
    co
    #
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @8
    c1
    caddc
    co
    #
    @5
    @6
    @4
    @9
    c1
    @8
    caddc
    @4
    c1
    @9
    @4
    c1
    cc
    wcel
    c1
    @9
    wceq
    ax-1cn
    cA
    c1
    mul02lem1
    mpan2
    eqcomd
    oveq2d
    @11
    c1
    caddc
    co
    @10
    @5
    @8
    c1
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulcli
    ax-1cn
    ax-1cn
    addassi
    @11
    cc0
    c1
    caddc
    ax-i2m1
    oveq1i
    eqtr3i
    @11
    cc0
    @6
    ax-i2m1
    00id
    eqtr4i
    3eqtr3g
    c1
    cr
    wcel
    cc0
    cr
    wcel
    #
    @12
    @7
    @3
    wb
    1re
    0re
    0re
    c1
    cc0
    cc0
    readdcan
    mp3an
    sylib
    ex
    necon1d
    mpi
end
