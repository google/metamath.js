include "wfun.mm"
include "c0.mm"
include "crn.mm"
include "wnel.mm"
include "wa.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "eldmrexrn.mm"
include "adantr.mm"
include "eleq1.mm"
include "wne.mm"
include "elnelne2.mm"
include "wex.mm"
include "n0.mm"
include "elfvdm.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"
include "expcom.mm"
include "adantl.mm"
include "com12.mm"
include "syl6bi.mm"
include "com13.mm"
include "rexlimdv.mm"
include "impbid.mm"

theorem eldmrexrnb
  let vx: setvar x
  let cF: class F
  let cY: class Y
  let vy: setvar y

  disjoint F x
  disjoint Y x
  disjoint F y
  disjoint x y
  disjoint Y y
  assert |- ( ( Fun F /\ (/) e/ ran F ) -> ( Y e. dom F <-> E. x e. ran F x = ( F ` Y ) ) )

  proof
    cF
    wfun
    #
    c0
    cF
    crn
    #
    wnel
    #
    wa
    #
    cY
    cF
    cdm
    wcel
    #
    vx
    cv
    #
    cY
    cF
    cfv
    #
    wceq
    #
    vx
    @1
    wrex
    #
    @0
    @4
    @8
    wi
    @2
    vx
    cF
    cY
    eldmrexrn
    adantr
    @3
    @7
    @4
    vx
    @1
    @7
    @5
    @1
    wcel
    #
    @3
    @4
    @7
    @9
    @6
    @1
    wcel
    #
    @3
    @4
    wi
    @5
    @6
    @1
    eleq1
    @3
    @10
    @4
    @2
    @10
    @4
    wi
    @0
    @10
    @2
    @4
    @10
    @2
    wa
    @6
    c0
    wne
    #
    @4
    @6
    c0
    @1
    elnelne2
    @11
    vy
    cv
    #
    @6
    wcel
    #
    vy
    wex
    @4
    vy
    @6
    n0
    @13
    @4
    vy
    @12
    cY
    cF
    elfvdm
    exlimiv
    sylbi
    syl
    expcom
    adantl
    com12
    syl6bi
    com13
    rexlimdv
    impbid
end
