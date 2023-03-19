include "wcel.mm"
include "ctsk.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "eltskg.mm"
include "nfra1.mm"
include "wi.mm"
include "weq.mm"
include "pweq.mm"
include "sseq1d.mm"
include "rspccva.mm"
include "adantlr.mm"
include "vpwex.mm"
include "elpw.mm"
include "ssel.mm"
include "syl5bir.mm"
include "syl.mm"
include "rexlimdva.mm"
include "ralimdaa.mm"
include "imdistani.mm"
include "r19.26.mm"
include "3imtr4i.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "anim2i.mm"
include "ralimi.mm"
include "impbii.mm"
include "anbi1i.mm"
include "syl6bb.mm"

theorem eltsk2g
  let vz: setvar z
  let cT: class T
  let cV: class V
  let cA: class A
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y

  disjoint T z
  disjoint A x
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( T e. V -> ( T e. Tarski <-> ( A. z e. T ( ~P z C_ T /\ ~P z e. T ) /\ A. z e. ~P T ( z ~~ T \/ z e. T ) ) ) )

  proof
    cT
    cV
    wcel
    cT
    ctsk
    wcel
    vz
    cv
    #
    cpw
    #
    cT
    wss
    #
    @1
    vw
    cv
    #
    wss
    #
    vw
    cT
    wrex
    #
    wa
    #
    vz
    cT
    wral
    #
    @0
    cT
    cen
    wbr
    @0
    cT
    wcel
    #
    wo
    vz
    cT
    cpw
    wral
    #
    wa
    @2
    @1
    cT
    wcel
    #
    wa
    #
    vz
    cT
    wral
    #
    @9
    wa
    vz
    vw
    cT
    cV
    eltskg
    @7
    @12
    @9
    @7
    @12
    @2
    vz
    cT
    wral
    #
    @5
    vz
    cT
    wral
    #
    wa
    @13
    @10
    vz
    cT
    wral
    #
    wa
    @7
    @12
    @13
    @14
    @15
    @13
    @5
    @10
    vz
    cT
    @2
    vz
    cT
    nfra1
    @13
    @8
    wa
    #
    @4
    @10
    vw
    cT
    @16
    @3
    cT
    wcel
    #
    wa
    @3
    cpw
    #
    cT
    wss
    #
    @4
    @10
    wi
    @13
    @17
    @19
    @8
    @2
    @19
    vz
    @3
    cT
    vz
    vw
    weq
    @1
    @18
    cT
    @0
    @3
    pweq
    sseq1d
    rspccva
    adantlr
    @4
    @1
    @18
    wcel
    @19
    @10
    @1
    @3
    vz
    vpwex
    elpw
    @18
    cT
    @1
    ssel
    syl5bir
    syl
    rexlimdva
    ralimdaa
    imdistani
    @2
    @5
    vz
    cT
    r19.26
    @2
    @10
    vz
    cT
    r19.26
    3imtr4i
    @11
    @6
    vz
    cT
    @10
    @5
    @2
    @10
    @1
    @1
    wss
    #
    @5
    @1
    ssid
    @4
    @20
    vw
    @1
    cT
    @3
    @1
    @1
    sseq2
    rspcev
    mpan2
    anim2i
    ralimi
    impbii
    anbi1i
    syl6bb
end
