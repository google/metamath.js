include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "chash.mm"
include "cfv.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "undif2.mm"
include "fveq2i.mm"
include "wceq.mm"
include "diffi.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "hashun.mm"
include "mp3an3.mm"
include "sylan2.mm"
include "syl5eqr.mm"
include "cn0.mm"
include "adantl.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "adantr.mm"
include "wbr.mm"
include "cdom.mm"
include "wss.mm"
include "simpr.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "wb.mm"
include "hashdom.mm"
include "sylancom.mm"
include "mpbird.mm"
include "leadd2dd.mm"
include "eqbrtrd.mm"

theorem hashun2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( # ` ( A u. B ) ) <_ ( ( # ` A ) + ( # ` B ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cB
    cA
    cdif
    #
    chash
    cfv
    #
    caddc
    co
    #
    @5
    cB
    chash
    cfv
    #
    caddc
    co
    cle
    @2
    @4
    cA
    @6
    cun
    #
    chash
    cfv
    #
    @8
    @10
    @3
    chash
    cA
    cB
    undif2
    fveq2i
    @1
    @0
    @6
    cfn
    wcel
    #
    @11
    @8
    wceq
    #
    cB
    cA
    diffi
    #
    @0
    @12
    cA
    @6
    cin
    c0
    wceq
    @13
    cA
    cB
    disjdif
    cA
    @6
    hashun
    mp3an3
    sylan2
    syl5eqr
    @2
    @7
    @9
    @5
    @2
    @7
    @2
    @12
    @7
    cn0
    wcel
    @1
    @12
    @0
    @14
    adantl
    #
    @6
    hashcl
    syl
    nn0red
    @2
    @9
    @1
    @9
    cn0
    wcel
    @0
    cB
    hashcl
    adantl
    nn0red
    @2
    @5
    @0
    @5
    cn0
    wcel
    @1
    cA
    hashcl
    adantr
    nn0red
    @2
    @7
    @9
    cle
    wbr
    #
    @6
    cB
    cdom
    wbr
    #
    @2
    @1
    @6
    cB
    wss
    @17
    @0
    @1
    simpr
    cB
    cA
    difss
    @6
    cB
    cfn
    ssdomg
    mpisyl
    @0
    @1
    @12
    @16
    @17
    wb
    @15
    @6
    cB
    cfn
    hashdom
    sylancom
    mpbird
    leadd2dd
    eqbrtrd
end
