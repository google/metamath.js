include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cmi.mm"
include "co.mm"
include "comu.mm"
include "mulpiord.mm"
include "com.mm"
include "c0.mm"
include "wne.mm"
include "pinn.mm"
include "nnmcl.mm"
include "syl2an.mm"
include "elni2.mm"
include "simprbi.mm"
include "adantl.mm"
include "wi.mm"
include "adantr.mm"
include "nnmordi.mm"
include "syl21anc.mm"
include "mpd.mm"
include "ne0i.mm"
include "syl.mm"
include "elni.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"

theorem mulclpi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. N. /\ B e. N. ) -> ( A .N B ) e. N. )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    #
    cA
    cB
    cmi
    co
    cA
    cB
    comu
    co
    #
    cnpi
    cA
    cB
    mulpiord
    @2
    @3
    com
    wcel
    #
    @3
    c0
    wne
    #
    @3
    cnpi
    wcel
    @0
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    @4
    @1
    cA
    pinn
    #
    cB
    pinn
    #
    cA
    cB
    nnmcl
    syl2an
    @2
    cA
    c0
    comu
    co
    #
    @3
    wcel
    #
    @5
    @2
    c0
    cB
    wcel
    #
    @11
    @1
    @12
    @0
    @1
    @7
    @12
    cB
    elni2
    simprbi
    adantl
    @2
    @7
    @6
    c0
    cA
    wcel
    #
    @12
    @11
    wi
    @1
    @7
    @0
    @9
    adantl
    @0
    @6
    @1
    @8
    adantr
    @0
    @13
    @1
    @0
    @6
    @13
    cA
    elni2
    simprbi
    adantr
    c0
    cB
    cA
    nnmordi
    syl21anc
    mpd
    @3
    @10
    ne0i
    syl
    @3
    elni
    sylanbrc
    eqeltrd
end
