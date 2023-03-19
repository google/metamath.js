include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "cle.mm"
include "abs3difi.mm"
include "subcli.mm"
include "abscli.mm"
include "rehalfcli.mm"
include "lt2addi.mm"
include "readdcli.mm"
include "lelttri.mm"
include "sylancr.mm"
include "cmul.mm"
include "recni.mm"
include "2timesi.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan2i.mm"
include "eqtr3i.mm"
include "syl6breq.mm"

theorem abs3lemi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume absvalsqi.1: |- A e. CC
  assume abssub.2: |- B e. CC
  assume abs3dif.3: |- C e. CC
  assume abs3lem.4: |- D e. RR


  assert |- ( ( ( abs ` ( A - C ) ) < ( D / 2 ) /\ ( abs ` ( C - B ) ) < ( D / 2 ) ) -> ( abs ` ( A - B ) ) < D )

  proof
    cA
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cD
    c2
    cdiv
    co
    #
    clt
    wbr
    cC
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @2
    clt
    wbr
    wa
    #
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @2
    @2
    caddc
    co
    #
    cD
    clt
    @5
    @7
    @1
    @4
    caddc
    co
    #
    cle
    wbr
    @9
    @8
    clt
    wbr
    @7
    @8
    clt
    wbr
    cA
    cB
    cC
    absvalsqi.1
    abssub.2
    abs3dif.3
    abs3difi
    @1
    @4
    @2
    @2
    @0
    cA
    cC
    absvalsqi.1
    abs3dif.3
    subcli
    abscli
    #
    @3
    cC
    cB
    abs3dif.3
    abssub.2
    subcli
    abscli
    #
    cD
    abs3lem.4
    rehalfcli
    #
    @12
    lt2addi
    @7
    @9
    @8
    @6
    cA
    cB
    absvalsqi.1
    abssub.2
    subcli
    abscli
    @1
    @4
    @10
    @11
    readdcli
    @2
    @2
    @12
    @12
    readdcli
    lelttri
    sylancr
    c2
    @2
    cmul
    co
    @8
    cD
    @2
    @2
    @12
    recni
    2timesi
    cD
    c2
    cD
    abs3lem.4
    recni
    2cn
    2ne0
    divcan2i
    eqtr3i
    syl6breq
end
