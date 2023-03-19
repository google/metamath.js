include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn0.mm"
include "wa.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "caddc.mm"
include "cmul.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "nncn.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "3jca.mm"
include "adantr.mm"
include "divcan2.mm"
include "eqcomd.mm"
include "syl.mm"
include "fveq2d.mm"
include "nn0enne.mm"
include "biimpa.mm"
include "blennnt2.mm"
include "eqtr2d.mm"
include "blennnelnn.mm"
include "nncnd.mm"
include "1cnd.mm"
include "blennn0elnn.mm"
include "adantl.mm"
include "subadd2d.mm"
include "mpbird.mm"

theorem blennn0em1
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( N / 2 ) e. NN0 ) -> ( #b ` ( N / 2 ) ) = ( ( #b ` N ) - 1 ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    wa
    #
    cN
    cblen
    cfv
    #
    c1
    cmin
    co
    #
    @1
    cblen
    cfv
    #
    @3
    @5
    @6
    wceq
    @6
    c1
    caddc
    co
    #
    @4
    wceq
    @3
    @4
    c2
    @1
    cmul
    co
    #
    cblen
    cfv
    #
    @7
    @3
    cN
    @8
    cblen
    @3
    cN
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    w3a
    #
    cN
    @8
    wceq
    @0
    @13
    @2
    @0
    @10
    @11
    @12
    cN
    nncn
    @0
    2cnd
    @12
    @0
    2ne0
    a1i
    3jca
    adantr
    @13
    @8
    cN
    cN
    c2
    divcan2
    eqcomd
    syl
    fveq2d
    @3
    @1
    cn
    wcel
    #
    @9
    @7
    wceq
    @0
    @2
    @14
    cN
    nn0enne
    biimpa
    @1
    blennnt2
    syl
    eqtr2d
    @3
    @4
    c1
    @6
    @0
    @4
    cc
    wcel
    @2
    @0
    @4
    cN
    blennnelnn
    nncnd
    adantr
    @3
    1cnd
    @2
    @6
    cc
    wcel
    @0
    @2
    @6
    @1
    blennn0elnn
    nncnd
    adantl
    subadd2d
    mpbird
    eqcomd
end
