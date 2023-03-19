include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cdif.mm"
include "wceq.mm"
include "caddc.mm"
include "cun.mm"
include "ssfi.mm"
include "diffi.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "hashun.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "anabss1.mm"
include "wb.mm"
include "undif.mm"
include "biimpi.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "cc.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "cn0.mm"
include "syl.mm"
include "subadd.mm"
include "syl3an.mm"
include "3anidm13.mm"
include "anabss5.mm"
include "mpbird.mm"

theorem hashssdif
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B C_ A ) -> ( # ` ( A \ B ) ) = ( ( # ` A ) - ( # ` B ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cmin
    co
    #
    cA
    cB
    cdif
    #
    chash
    cfv
    #
    @2
    @5
    @7
    wceq
    #
    @4
    @7
    caddc
    co
    #
    @3
    wceq
    #
    @2
    @3
    @9
    @2
    cB
    @6
    cun
    #
    chash
    cfv
    #
    @9
    wceq
    #
    @3
    @9
    wceq
    #
    @0
    @1
    @13
    @2
    cB
    cfn
    wcel
    #
    @6
    cfn
    wcel
    #
    @13
    @0
    cA
    cB
    ssfi
    #
    cA
    cB
    diffi
    #
    @15
    @16
    cB
    @6
    cin
    c0
    wceq
    @13
    cB
    cA
    disjdif
    cB
    @6
    hashun
    mp3an3
    syl2an
    anabss1
    @1
    @13
    @14
    wb
    @0
    @1
    @12
    @3
    @9
    @1
    @11
    cA
    chash
    @1
    @11
    cA
    wceq
    cB
    cA
    undif
    biimpi
    fveq2d
    eqeq1d
    adantl
    mpbid
    eqcomd
    @0
    @1
    @8
    @10
    wb
    #
    @0
    @2
    @19
    @0
    @3
    cc
    wcel
    @2
    @4
    cc
    wcel
    @0
    @7
    cc
    wcel
    @19
    @0
    @3
    cA
    hashcl
    nn0cnd
    @2
    @4
    @2
    @15
    @4
    cn0
    wcel
    @17
    cB
    hashcl
    syl
    nn0cnd
    @0
    @7
    @0
    @16
    @7
    cn0
    wcel
    @18
    @6
    hashcl
    syl
    nn0cnd
    @3
    @4
    @7
    subadd
    syl3an
    3anidm13
    anabss5
    mpbird
    eqcomd
end
