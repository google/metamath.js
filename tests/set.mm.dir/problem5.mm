include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "c6.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c9.mm"
include "cmin.mm"
include "caddc.mm"
include "2re.mm"
include "remulcli.mm"
include "3re.mm"
include "9re.mm"
include "ltaddsubi.mm"
include "mpbi.mm"
include "3cn.mm"
include "6cn.mm"
include "6p3e9.mm"
include "addcomi.mm"
include "eqtr3i.mm"
include "eqcomi.mm"
include "mvlladdi.mm"
include "breqtri.mm"
include "6re.mm"
include "2nn.mm"
include "nngt0i.mm"
include "ltdiv1ii.mm"
include "recni.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3i.mm"
include "wceq.mm"
include "mulcomi.mm"
include "3t2e6.mm"
include "eqtri.mm"
include "divmuli.mm"
include "mpbir.mm"
include "3brtr3i.mm"

theorem problem5
  let cA: class A
  assume problem5.1: |- A e. RR
  assume problem5.2: |- ( ( 2 x. A ) + 3 ) < 9


  assert |- A < 3

  proof
    c2
    cA
    cmul
    co
    #
    c2
    cdiv
    co
    #
    c6
    c2
    cdiv
    co
    #
    cA
    c3
    clt
    @0
    c6
    clt
    wbr
    @1
    @2
    clt
    wbr
    @0
    c9
    c3
    cmin
    co
    #
    c6
    clt
    @0
    c3
    caddc
    co
    c9
    clt
    wbr
    @0
    @3
    clt
    wbr
    problem5.2
    @0
    c3
    c9
    c2
    cA
    2re
    problem5.1
    remulcli
    #
    3re
    9re
    ltaddsubi
    mpbi
    c6
    @3
    c3
    c6
    c9
    3cn
    6cn
    c9
    c3
    c6
    caddc
    co
    #
    c6
    c3
    caddc
    co
    c9
    @5
    6p3e9
    c6
    c3
    6cn
    3cn
    addcomi
    eqtr3i
    eqcomi
    mvlladdi
    eqcomi
    breqtri
    @0
    c6
    c2
    @4
    6re
    2re
    c2
    2nn
    nngt0i
    ltdiv1ii
    mpbi
    cA
    c2
    cA
    problem5.1
    recni
    2cn
    2ne0
    divcan3i
    @2
    c3
    wceq
    c2
    c3
    cmul
    co
    #
    c6
    wceq
    @6
    c3
    c2
    cmul
    co
    c6
    c2
    c3
    2cn
    3cn
    mulcomi
    3t2e6
    eqtri
    c6
    c2
    c3
    6cn
    2cn
    3cn
    2ne0
    divmuli
    mpbir
    3brtr3i
end
