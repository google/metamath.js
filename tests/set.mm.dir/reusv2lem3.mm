include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "weu.mm"
include "wa.mm"
include "simpr.mm"
include "nfv.mm"
include "nfeu1.mm"
include "nfan.mm"
include "wi.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "euex.mm"
include "rexn0.mm"
include "exlimiv.mm"
include "r19.2z.mm"
include "ex.mm"
include "3syl.mm"
include "adantl.mm"
include "nfra1.mm"
include "nfre1.mm"
include "nfeu.mm"
include "rsp.mm"
include "impcom.mm"
include "isset.mm"
include "sylib.mm"
include "adantrr.mm"
include "rspe.mm"
include "ancrd.mm"
include "eximdv.mm"
include "imp.mm"
include "syldan.mm"
include "eupick.mm"
include "syl2an2.mm"
include "com3l.mm"
include "ralrimd.mm"
include "impbid.mm"
include "eubid.mm"
include "mpbird.mm"
include "reusv2lem2.mm"
include "impbid1.mm"

theorem reusv2lem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let cC: class C
  let wph: wff ph

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint ph x
  disjoint ph z
  assert |- ( A. y e. A B e. _V -> ( E! x E. y e. A x = B <-> E! x A. y e. A x = B ) )

  proof
    cB
    cvv
    wcel
    #
    vy
    cA
    wral
    #
    vx
    cv
    cB
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    weu
    #
    @2
    vy
    cA
    wral
    #
    vx
    weu
    #
    @1
    @4
    @6
    @1
    @4
    wa
    #
    @6
    @4
    @1
    @4
    simpr
    #
    @7
    @5
    @3
    vx
    @1
    @4
    vx
    @1
    vx
    nfv
    @3
    vx
    nfeu1
    nfan
    @7
    @5
    @3
    @4
    @5
    @3
    wi
    #
    @1
    @4
    @3
    vx
    wex
    cA
    c0
    wne
    #
    @9
    @3
    vx
    euex
    @3
    @10
    vx
    @2
    vy
    cA
    rexn0
    exlimiv
    @10
    @5
    @3
    @2
    vy
    cA
    r19.2z
    ex
    3syl
    adantl
    @7
    @3
    @2
    vy
    cA
    @1
    @4
    vy
    @0
    vy
    cA
    nfra1
    @3
    vy
    vx
    @2
    vy
    cA
    nfre1
    #
    nfeu
    nfan
    @11
    vy
    cv
    cA
    wcel
    #
    @7
    @3
    @2
    @12
    @7
    @3
    @2
    wi
    #
    @7
    @4
    @12
    @3
    @2
    wa
    #
    vx
    wex
    #
    @13
    @8
    @12
    @7
    @2
    vx
    wex
    #
    @15
    @12
    @1
    @16
    @4
    @12
    @1
    wa
    @0
    @16
    @1
    @12
    @0
    @0
    vy
    cA
    rsp
    impcom
    vx
    cB
    isset
    sylib
    adantrr
    @12
    @16
    @15
    @12
    @2
    @14
    vx
    @12
    @2
    @3
    @12
    @2
    @3
    @2
    vy
    cA
    rspe
    ex
    ancrd
    eximdv
    imp
    syldan
    @3
    @2
    vx
    eupick
    syl2an2
    ex
    com3l
    ralrimd
    impbid
    eubid
    mpbird
    ex
    vx
    vy
    cA
    cB
    reusv2lem2
    impbid1
end
