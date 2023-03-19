include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cc0.mm"
include "wceq.mm"
include "cneg.mm"
include "1p1times.mm"
include "negid.mm"
include "ax-1cn.mm"
include "addcli.mm"
include "mul01i.mm"
include "syl6reqr.mm"
include "eqeq12d.mm"
include "id.mm"
include "0cnd.mm"
include "a1i.mm"
include "wne.mm"
include "1re.mm"
include "readdcli.mm"
include "0lt1.mm"
include "addgt0ii.mm"
include "gt0ne0ii.mm"
include "mulcand.mm"
include "negcl.mm"
include "addcand.mm"
include "3bitr3rd.mm"

theorem eqneg
  let cA: class A


  assert |- ( A e. CC -> ( A = -u A <-> A = 0 ) )

  proof
    cA
    cc
    wcel
    #
    c1
    c1
    caddc
    co
    #
    cA
    cmul
    co
    #
    @1
    cc0
    cmul
    co
    #
    wceq
    cA
    cA
    caddc
    co
    #
    cA
    cA
    cneg
    #
    caddc
    co
    #
    wceq
    cA
    cc0
    wceq
    cA
    @5
    wceq
    @0
    @2
    @4
    @3
    @6
    cA
    1p1times
    @0
    @6
    cc0
    @3
    cA
    negid
    @1
    c1
    c1
    ax-1cn
    ax-1cn
    addcli
    #
    mul01i
    syl6reqr
    eqeq12d
    @0
    cA
    cc0
    @1
    @0
    id
    #
    @0
    0cnd
    @1
    cc
    wcel
    @0
    @7
    a1i
    @1
    cc0
    wne
    @0
    @1
    c1
    c1
    1re
    1re
    readdcli
    c1
    c1
    1re
    1re
    0lt1
    0lt1
    addgt0ii
    gt0ne0ii
    a1i
    mulcand
    @0
    cA
    cA
    @5
    @8
    @8
    cA
    negcl
    addcand
    3bitr3rd
end
