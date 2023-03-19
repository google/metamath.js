include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "cle.mm"
include "norm3difi.mm"
include "hvsubcli.mm"
include "normcli.mm"
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

theorem norm3lem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume norm3dif.1: |- A e. ~H
  assume norm3dif.2: |- B e. ~H
  assume norm3dif.3: |- C e. ~H
  assume norm3lem.4: |- D e. RR


  assert |- ( ( ( normh ` ( A -h C ) ) < ( D / 2 ) /\ ( normh ` ( C -h B ) ) < ( D / 2 ) ) -> ( normh ` ( A -h B ) ) < D )

  proof
    cA
    cC
    cmv
    co
    #
    cno
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
    cmv
    co
    #
    cno
    cfv
    #
    @2
    clt
    wbr
    wa
    #
    cA
    cB
    cmv
    co
    #
    cno
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
    norm3dif.1
    norm3dif.2
    norm3dif.3
    norm3difi
    @1
    @4
    @2
    @2
    @0
    cA
    cC
    norm3dif.1
    norm3dif.3
    hvsubcli
    normcli
    #
    @3
    cC
    cB
    norm3dif.3
    norm3dif.2
    hvsubcli
    normcli
    #
    cD
    norm3lem.4
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
    norm3dif.1
    norm3dif.2
    hvsubcli
    normcli
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
    norm3lem.4
    recni
    2cn
    2ne0
    divcan2i
    eqtr3i
    syl6breq
end
