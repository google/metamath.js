include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "cpw.mm"
include "crab.mm"
include "cfcls.mm"
include "co.mm"
include "wn.mm"
include "disjdif.mm"
include "wne.mm"
include "wa.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "difss.mm"
include "wb.mm"
include "simpl1.mm"
include "toponmax.mm"
include "elpw2g.mm"
include "3syl.mm"
include "mpbiri.mm"
include "ssid.mm"
include "a1i.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fclsopni.mm"
include "syl13anc.mm"
include "ex.mm"
include "necon2bd.mm"
include "mpi.mm"

theorem supnfcls
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cJ: class J
  let cX: class X
  let vn: setvar n
  let vo: setvar o
  let vs: setvar s
  let cF: class F
  let cS: class S

  disjoint J x
  disjoint X x
  disjoint U x
  disjoint n o
  disjoint n s
  disjoint A n
  disjoint o s
  disjoint A o
  disjoint A s
  disjoint n x
  disjoint F n
  disjoint o x
  disjoint F o
  disjoint s x
  disjoint F s
  disjoint F x
  disjoint J n
  disjoint J o
  disjoint J s
  disjoint S s
  disjoint S x
  disjoint X o
  disjoint X s
  assert |- ( ( J e. ( TopOn ` X ) /\ U e. J /\ A e. U ) -> -. A e. ( J fClus { x e. ~P X | ( X \ U ) C_ x } ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cU
    cJ
    wcel
    #
    cA
    cU
    wcel
    #
    w3a
    #
    cU
    cX
    cU
    cdif
    #
    cin
    #
    c0
    wceq
    cA
    cJ
    @4
    vx
    cv
    #
    wss
    #
    vx
    cX
    cpw
    #
    crab
    #
    cfcls
    co
    wcel
    #
    wn
    cU
    cX
    disjdif
    @3
    @10
    @5
    c0
    @3
    @10
    @5
    c0
    wne
    #
    @3
    @10
    wa
    #
    @10
    @1
    @2
    @4
    @9
    wcel
    #
    @11
    @3
    @10
    simpr
    @0
    @1
    @2
    @10
    simpl2
    @0
    @1
    @2
    @10
    simpl3
    @12
    @4
    @8
    wcel
    #
    @4
    @4
    wss
    #
    @13
    @12
    @14
    @4
    cX
    wss
    #
    cX
    cU
    difss
    @12
    @0
    cX
    cJ
    wcel
    @14
    @16
    wb
    @0
    @1
    @2
    @10
    simpl1
    cX
    cJ
    toponmax
    @4
    cX
    cJ
    elpw2g
    3syl
    mpbiri
    @15
    @12
    @4
    ssid
    a1i
    @7
    @15
    vx
    @4
    @8
    @6
    @4
    @4
    sseq2
    elrab
    sylanbrc
    cA
    @4
    cU
    @9
    cJ
    fclsopni
    syl13anc
    ex
    necon2bd
    mpi
end
