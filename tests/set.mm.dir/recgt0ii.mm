include "cc0.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "ax-1cn.mm"
include "recni.mm"
include "ax-1ne0.mm"
include "gt0ne0ii.mm"
include "divne0i.mm"
include "nesymi.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnsymi.mm"
include "ax-mp.mm"
include "cneg.mm"
include "cmul.mm"
include "rereccli.mm"
include "renegcli.mm"
include "mulgt0i.mm"
include "mpan2.mm"
include "mulneg1i.mm"
include "recidi.mm"
include "mulcomli.mm"
include "negeqi.mm"
include "eqtri.mm"
include "syl6breq.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "lt0neg1.mm"
include "3imtr4i.mm"
include "mto.mm"
include "pm3.2ni.mm"
include "axlttri.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem recgt0ii
  let cA: class A
  assume ltplus1.1: |- A e. RR
  assume recgt0i.2: |- 0 < A


  assert |- 0 < ( 1 / A )

  proof
    cc0
    c1
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    cc0
    @0
    wceq
    #
    @0
    cc0
    clt
    wbr
    #
    wo
    wn
    #
    @2
    @3
    @0
    cc0
    c1
    cA
    ax-1cn
    cA
    ltplus1.1
    recni
    #
    ax-1ne0
    cA
    ltplus1.1
    recgt0i.2
    gt0ne0ii
    #
    divne0i
    nesymi
    @3
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    clt
    wbr
    @7
    wn
    0lt1
    cc0
    c1
    0re
    1re
    ltnsymi
    ax-mp
    cc0
    @0
    cneg
    #
    clt
    wbr
    #
    cc0
    c1
    cneg
    #
    clt
    wbr
    #
    @3
    @7
    @9
    cc0
    @8
    cA
    cmul
    co
    #
    @10
    clt
    @9
    cc0
    cA
    clt
    wbr
    cc0
    @12
    clt
    wbr
    recgt0i.2
    @8
    cA
    @0
    cA
    ltplus1.1
    @6
    rereccli
    #
    renegcli
    ltplus1.1
    mulgt0i
    mpan2
    @12
    @0
    cA
    cmul
    co
    #
    cneg
    @10
    @0
    cA
    @0
    @13
    recni
    #
    @5
    mulneg1i
    @14
    c1
    cA
    @0
    c1
    @5
    @15
    cA
    @5
    @6
    recidi
    mulcomli
    negeqi
    eqtri
    syl6breq
    @0
    cr
    wcel
    #
    @3
    @9
    wb
    @13
    @0
    lt0neg1
    ax-mp
    c1
    cr
    wcel
    @7
    @11
    wb
    1re
    c1
    lt0neg1
    ax-mp
    3imtr4i
    mto
    pm3.2ni
    cc0
    cr
    wcel
    @16
    @1
    @4
    wb
    0re
    @13
    cc0
    @0
    axlttri
    mp2an
    mpbir
end
