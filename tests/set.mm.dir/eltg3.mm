include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cpw.mm"
include "cin.mm"
include "cvv.mm"
include "cdm.mm"
include "elfvdm.mm"
include "inex1g.mm"
include "syl.mm"
include "eltg4i.mm"
include "inss1.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "biantrurd.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "bitr3d.mm"
include "spcegv.mm"
include "sylc.mm"
include "eltg3i.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "impbid2.mm"

theorem eltg3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint V x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint C y
  assert |- ( B e. V -> ( A e. ( topGen ` B ) <-> E. x ( x C_ B /\ A = U. x ) ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    ctg
    cfv
    #
    wcel
    #
    vx
    cv
    #
    cB
    wss
    #
    cA
    @3
    cuni
    #
    wceq
    #
    wa
    #
    vx
    wex
    #
    @2
    cB
    cA
    cpw
    #
    cin
    #
    cvv
    wcel
    #
    cA
    @10
    cuni
    #
    wceq
    #
    @8
    @2
    cB
    ctg
    cdm
    #
    wcel
    @11
    cA
    cB
    ctg
    elfvdm
    cB
    @9
    @14
    inex1g
    syl
    cA
    cB
    eltg4i
    @7
    @13
    vx
    @10
    cvv
    @3
    @10
    wceq
    #
    @6
    @7
    @13
    @15
    @4
    @6
    @15
    @4
    @10
    cB
    wss
    cB
    @9
    inss1
    @3
    @10
    cB
    sseq1
    mpbiri
    biantrurd
    @15
    @5
    @12
    cA
    @3
    @10
    unieq
    eqeq2d
    bitr3d
    spcegv
    sylc
    @0
    @7
    @2
    vx
    @0
    @4
    @6
    @2
    @0
    @4
    wa
    @2
    @6
    @5
    @1
    wcel
    @3
    cB
    cV
    eltg3i
    cA
    @5
    @1
    eleq1
    syl5ibrcom
    expimpd
    exlimdv
    impbid2
end
