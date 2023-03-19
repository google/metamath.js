include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "weu.mm"
include "wnfc.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "eusvnf.mm"
include "wex.mm"
include "euex.mm"
include "eqvisset.mm"
include "sps.mm"
include "exlimiv.mm"
include "syl.mm"
include "jca.mm"
include "isset.mm"
include "nfcvd.mm"
include "id.mm"
include "nfeqd.mm"
include "nf5rd.mm"
include "eximdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "eusv1.mm"
include "sylibr.mm"
include "impbii.mm"

theorem eusvnfb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( E! y A. x y = A <-> ( F/_ x A /\ A e. _V ) )

  proof
    vy
    cv
    #
    cA
    wceq
    #
    vx
    wal
    #
    vy
    weu
    #
    vx
    cA
    wnfc
    #
    cA
    cvv
    wcel
    #
    wa
    #
    @3
    @4
    @5
    vx
    vy
    cA
    eusvnf
    @3
    @2
    vy
    wex
    #
    @5
    @2
    vy
    euex
    @2
    @5
    vy
    @1
    @5
    vx
    vy
    cA
    eqvisset
    sps
    exlimiv
    syl
    jca
    @6
    @7
    @3
    @4
    @5
    @7
    @5
    @1
    vy
    wex
    @4
    @7
    vy
    cA
    isset
    @4
    @1
    @2
    vy
    @4
    @1
    vx
    @4
    vx
    @0
    cA
    @4
    vx
    @0
    nfcvd
    @4
    id
    nfeqd
    nf5rd
    eximdv
    syl5bi
    imp
    vx
    vy
    cA
    eusv1
    sylibr
    impbii
end
