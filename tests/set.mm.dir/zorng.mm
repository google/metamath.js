include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "crpss.mm"
include "wor.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wpss.mm"
include "wceq.mm"
include "wo.mm"
include "risset.mm"
include "eqimss2.mm"
include "unissb.mm"
include "sylib.mm"
include "vex.mm"
include "brrpss.mm"
include "orbi1i.mm"
include "sspss.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "sylibr.mm"
include "reximi.mm"
include "sylbi.mm"
include "imim2i.mm"
include "alimi.mm"
include "wpo.mm"
include "porpss.mm"
include "zorn2g.mm"
include "mp3an2.mm"
include "sylan2.mm"
include "notbii.mm"
include "rexbii.mm"

theorem zorng
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cR: class R

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint g x
  disjoint h x
  disjoint t x
  disjoint s x
  disjoint r x
  disjoint q x
  disjoint d x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint R x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint g y
  disjoint h y
  disjoint t y
  disjoint s y
  disjoint r y
  disjoint q y
  disjoint d y
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint R y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint g z
  disjoint h z
  disjoint t z
  disjoint s z
  disjoint r z
  disjoint q z
  disjoint d z
  disjoint k z
  disjoint m z
  disjoint n z
  disjoint R z
  disjoint v w
  disjoint u w
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint s w
  disjoint r w
  disjoint q w
  disjoint d w
  disjoint k w
  disjoint m w
  disjoint n w
  disjoint R w
  disjoint u v
  disjoint g v
  disjoint h v
  disjoint t v
  disjoint s v
  disjoint r v
  disjoint q v
  disjoint d v
  disjoint k v
  disjoint m v
  disjoint n v
  disjoint R v
  disjoint g u
  disjoint h u
  disjoint t u
  disjoint s u
  disjoint r u
  disjoint q u
  disjoint d u
  disjoint k u
  disjoint m u
  disjoint n u
  disjoint R u
  disjoint g h
  disjoint g t
  disjoint g s
  disjoint g r
  disjoint g q
  disjoint d g
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint R g
  disjoint h t
  disjoint h s
  disjoint h r
  disjoint h q
  disjoint d h
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint R h
  disjoint s t
  disjoint r t
  disjoint q t
  disjoint d t
  disjoint k t
  disjoint m t
  disjoint n t
  disjoint R t
  disjoint r s
  disjoint q s
  disjoint d s
  disjoint k s
  disjoint m s
  disjoint n s
  disjoint R s
  disjoint q r
  disjoint d r
  disjoint k r
  disjoint m r
  disjoint n r
  disjoint R r
  disjoint d q
  disjoint k q
  disjoint m q
  disjoint n q
  disjoint R q
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint R d
  disjoint k m
  disjoint k n
  disjoint R k
  disjoint m n
  disjoint R m
  disjoint R n
  disjoint A w
  disjoint A v
  disjoint A u
  disjoint A g
  disjoint A h
  disjoint A t
  disjoint A s
  disjoint A r
  disjoint A q
  disjoint A d
  disjoint A k
  disjoint A m
  disjoint A n
  assert |- ( ( A e. dom card /\ A. z ( ( z C_ A /\ [C.] Or z ) -> U. z e. A ) ) -> E. x e. A A. y e. A -. x C. y )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    vz
    cv
    #
    cA
    wss
    @1
    crpss
    wor
    wa
    #
    @1
    cuni
    #
    cA
    wcel
    #
    wi
    #
    vz
    wal
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    crpss
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @7
    @8
    wpss
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    @6
    @0
    @2
    vu
    cv
    #
    @7
    crpss
    wbr
    #
    @16
    @7
    wceq
    #
    wo
    #
    vu
    @1
    wral
    #
    vx
    cA
    wrex
    #
    wi
    #
    vz
    wal
    #
    @12
    @5
    @22
    vz
    @4
    @21
    @2
    @4
    @7
    @3
    wceq
    #
    vx
    cA
    wrex
    @21
    vx
    @3
    cA
    risset
    @24
    @20
    vx
    cA
    @24
    @16
    @7
    wss
    #
    vu
    @1
    wral
    #
    @20
    @24
    @3
    @7
    wss
    @26
    @3
    @7
    eqimss2
    vu
    @1
    @7
    unissb
    sylib
    @19
    @25
    vu
    @1
    @19
    @16
    @7
    wpss
    #
    @18
    wo
    @25
    @17
    @27
    @18
    @16
    @7
    vx
    vex
    brrpss
    orbi1i
    @16
    @7
    sspss
    bitr4i
    ralbii
    sylibr
    reximi
    sylbi
    imim2i
    alimi
    @0
    cA
    crpss
    wpo
    @23
    @12
    cA
    porpss
    vx
    vy
    vu
    vz
    cA
    crpss
    zorn2g
    mp3an2
    sylan2
    @11
    @15
    vx
    cA
    @10
    @14
    vy
    cA
    @9
    @13
    @7
    @8
    vy
    vex
    brrpss
    notbii
    ralbii
    rexbii
    sylib
end
