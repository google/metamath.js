include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "crp.mm"
include "df-dp2.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "nn0rei.mm"
include "rpssre.mm"
include "cn.mm"
include "10nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "rpdivcl.mm"
include "mp2an.mm"
include "sselii.mm"
include "readdcl.mm"
include "wa.mm"
include "cle.mm"
include "pm3.2i.mm"
include "nn0ge0i.mm"
include "rpgt0.mm"
include "addgegt0.mm"
include "elrp.mm"
include "mpbir2an.mm"
include "eqeltri.mm"

theorem rpdp2cl
  let cA: class A
  let cB: class B
  assume rpdp2cl.a: |- A e. NN0
  assume rpdp2cl.b: |- B e. RR+


  assert |- _ A B e. RR+

  proof
    cA
    cB
    cdp2
    cA
    cB
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    #
    crp
    cA
    cB
    df-dp2
    @2
    crp
    wcel
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    cA
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @3
    cA
    rpdp2cl.a
    nn0rei
    #
    crp
    cr
    @1
    rpssre
    cB
    crp
    wcel
    @0
    crp
    wcel
    #
    @1
    crp
    wcel
    #
    rpdp2cl.b
    @0
    cn
    wcel
    @8
    10nn
    @0
    nnrp
    ax-mp
    cB
    @0
    rpdivcl
    mp2an
    #
    sselii
    #
    cA
    @1
    readdcl
    mp2an
    @5
    @6
    wa
    cc0
    cA
    cle
    wbr
    #
    cc0
    @1
    clt
    wbr
    #
    wa
    @4
    @5
    @6
    @7
    @11
    pm3.2i
    @12
    @13
    cA
    rpdp2cl.a
    nn0ge0i
    @9
    @13
    @10
    @1
    rpgt0
    ax-mp
    pm3.2i
    cA
    @1
    addgegt0
    mp2an
    @2
    elrp
    mpbir2an
    eqeltri
end
