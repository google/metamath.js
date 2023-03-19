include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "c0.mm"
include "wn.mm"
include "cv.mm"
include "cin.mm"
include "wne.mm"
include "wral.mm"
include "trfbas2.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "cdm.mm"
include "elfvdm.mm"
include "ssexg.mm"
include "ancoms.mm"
include "sylan.mm"
include "elrest.mm"
include "syldan.mm"
include "notbid.mm"
include "nesym.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem trfbas
  let vv: setvar v
  let cA: class A
  let cF: class F
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A v
  disjoint F v
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( F e. ( fBas ` Y ) /\ A C_ Y ) -> ( ( F |`t A ) e. ( fBas ` A ) <-> A. v e. F ( v i^i A ) =/= (/) ) )

  proof
    cF
    cY
    cfbas
    cfv
    #
    wcel
    #
    cA
    cY
    wss
    #
    wa
    #
    cF
    cA
    crest
    co
    #
    cA
    cfbas
    cfv
    wcel
    c0
    @4
    wcel
    #
    wn
    #
    vv
    cv
    cA
    cin
    #
    c0
    wne
    #
    vv
    cF
    wral
    #
    cA
    cF
    cY
    trfbas2
    @3
    @6
    c0
    @7
    wceq
    #
    vv
    cF
    wrex
    #
    wn
    #
    @9
    @3
    @5
    @11
    @1
    @2
    cA
    cvv
    wcel
    #
    @5
    @11
    wb
    @1
    cY
    cfbas
    cdm
    #
    wcel
    #
    @2
    @13
    cF
    cY
    cfbas
    elfvdm
    @2
    @15
    @13
    cA
    cY
    @14
    ssexg
    ancoms
    sylan
    vv
    c0
    cA
    cF
    @0
    cvv
    elrest
    syldan
    notbid
    @9
    @10
    wn
    #
    vv
    cF
    wral
    @12
    @8
    @16
    vv
    cF
    @7
    c0
    nesym
    ralbii
    @10
    vv
    cF
    ralnex
    bitri
    syl6bbr
    bitrd
end
