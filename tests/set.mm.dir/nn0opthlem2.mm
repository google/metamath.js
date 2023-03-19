include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "wne.mm"
include "c2.mm"
include "nn0addcli.mm"
include "nn0opthlem1.mm"
include "cle.mm"
include "nn0rei.mm"
include "nn0addge2i.mm"
include "nn0lele2xi.mm"
include "2re.mm"
include "remulcli.mm"
include "leadd2i.mm"
include "sylib.mm"
include "ax-mp.mm"
include "readdcli.mm"
include "lelttri.mm"
include "mpan.mm"
include "sylbi.mm"
include "nn0addge1i.mm"
include "ltletri.mm"
include "mpan2.mm"
include "ltnei.mm"
include "3syl.mm"

theorem nn0opthlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume nn0opth.1: |- A e. NN0
  assume nn0opth.2: |- B e. NN0
  assume nn0opth.3: |- C e. NN0
  assume nn0opth.4: |- D e. NN0


  assert |- ( ( A + B ) < C -> ( ( C x. C ) + D ) =/= ( ( ( A + B ) x. ( A + B ) ) + B ) )

  proof
    cA
    cB
    caddc
    co
    #
    cC
    clt
    wbr
    #
    @0
    @0
    cmul
    co
    #
    cB
    caddc
    co
    #
    cC
    cC
    cmul
    co
    #
    clt
    wbr
    #
    @3
    @4
    cD
    caddc
    co
    #
    clt
    wbr
    #
    @6
    @3
    wne
    @1
    @2
    c2
    @0
    cmul
    co
    #
    caddc
    co
    #
    @4
    clt
    wbr
    #
    @5
    @0
    cC
    cA
    cB
    nn0opth.1
    nn0opth.2
    nn0addcli
    #
    nn0opth.3
    nn0opthlem1
    @3
    @9
    cle
    wbr
    #
    @10
    @5
    cB
    @0
    cle
    wbr
    #
    @12
    cB
    cA
    cB
    nn0opth.2
    nn0rei
    #
    nn0opth.1
    nn0addge2i
    @13
    cB
    @8
    cle
    wbr
    @12
    @0
    cB
    @11
    nn0opth.2
    nn0lele2xi
    cB
    @8
    @2
    @14
    c2
    @0
    2re
    @0
    @11
    nn0rei
    #
    remulcli
    #
    @0
    @0
    @15
    @15
    remulcli
    #
    leadd2i
    sylib
    ax-mp
    @3
    @9
    @4
    @2
    cB
    @17
    @14
    readdcli
    #
    @2
    @8
    @17
    @16
    readdcli
    cC
    cC
    cC
    nn0opth.3
    nn0rei
    #
    @19
    remulcli
    #
    lelttri
    mpan
    sylbi
    @5
    @4
    @6
    cle
    wbr
    @7
    @4
    cD
    @20
    nn0opth.4
    nn0addge1i
    @3
    @4
    @6
    @18
    @20
    @4
    cD
    @20
    cD
    nn0opth.4
    nn0rei
    readdcli
    #
    ltletri
    mpan2
    @3
    @6
    @18
    @21
    ltnei
    3syl
end
