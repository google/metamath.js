include "wel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wi.mm"
include "nfeq2.mm"
include "eleq2.mm"
include "syl6bi.mm"
include "alrimi.mm"
include "nfv.mm"
include "axrep5.mm"
include "syl.mm"
include "anbi1d.mm"
include "exbid.mm"
include "bibi2d.mm"
include "albidv.mm"
include "exbidv.mm"
include "mpbid.mm"
include "vtocle.mm"

theorem zfrepclf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  assume zfrepclf.1: |- F/_ x A
  assume zfrepclf.2: |- A e. _V
  assume zfrepclf.3: |- ( x e. A -> E. z A. y ( ph -> y = z ) )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint ph v
  disjoint v x
  assert |- E. z A. y ( y e. z <-> E. x ( x e. A /\ ph ) )

  proof
    vy
    vz
    wel
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wex
    #
    wb
    #
    vy
    wal
    #
    vz
    wex
    #
    vv
    cA
    zfrepclf.2
    vv
    cv
    #
    cA
    wceq
    #
    @0
    vx
    vv
    wel
    #
    wph
    wa
    #
    vx
    wex
    #
    wb
    #
    vy
    wal
    #
    vz
    wex
    #
    @7
    @9
    @10
    wph
    vy
    cv
    vz
    cv
    wceq
    wi
    vy
    wal
    vz
    wex
    #
    wi
    #
    vx
    wal
    @15
    @9
    @17
    vx
    vx
    @8
    cA
    zfrepclf.1
    nfeq2
    #
    @9
    @10
    @2
    @16
    @8
    cA
    @1
    eleq2
    #
    zfrepclf.3
    syl6bi
    alrimi
    wph
    vx
    vy
    vz
    vv
    wph
    vz
    nfv
    axrep5
    syl
    @9
    @14
    @6
    vz
    @9
    @13
    @5
    vy
    @9
    @12
    @4
    @0
    @9
    @11
    @3
    vx
    @18
    @9
    @10
    @2
    wph
    @19
    anbi1d
    exbid
    bibi2d
    albidv
    exbidv
    mpbid
    vtocle
end
