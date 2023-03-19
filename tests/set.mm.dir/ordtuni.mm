include "wcel.mm"
include "csn.mm"
include "cuni.mm"
include "cun.mm"
include "cvv.mm"
include "wceq.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "unisng.mm"
include "syl.mm"
include "uneq1d.mm"
include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "wa.mm"
include "ssrab2.mm"
include "wb.mm"
include "adantr.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl5eqss.mm"
include "unssd.mm"
include "sspwuni.mm"
include "sylib.mm"
include "ssequn2.mm"
include "eqtr2d.mm"
include "uniun.mm"
include "syl6eqr.mm"

theorem ordtuni
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  assume ordtval.1: |- X = dom R
  assume ordtval.2: |- A = ran ( x e. X |-> { y e. X | -. y R x } )
  assume ordtval.3: |- B = ran ( x e. X |-> { y e. X | -. x R y } )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint V x
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a w
  disjoint a z
  disjoint A a
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint m n
  disjoint m r
  disjoint m w
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n w
  disjoint n z
  disjoint A n
  disjoint r w
  disjoint r z
  disjoint A r
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint a x
  disjoint a y
  disjoint R a
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint m x
  disjoint m y
  disjoint R m
  disjoint n x
  disjoint n y
  disjoint R n
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint w x
  disjoint w y
  disjoint R w
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X w
  disjoint X z
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B z
  disjoint C m
  disjoint C n
  disjoint C z
  assert |- ( R e. V -> X = U. ( { X } u. ( A u. B ) ) )

  proof
    cR
    cV
    wcel
    #
    cX
    cX
    csn
    #
    cuni
    #
    cA
    cB
    cun
    #
    cuni
    #
    cun
    #
    @1
    @3
    cun
    cuni
    @0
    @5
    cX
    @4
    cun
    #
    cX
    @0
    @2
    cX
    @4
    @0
    cX
    cvv
    wcel
    #
    @2
    cX
    wceq
    @0
    cX
    cR
    cdm
    cvv
    ordtval.1
    cR
    cV
    dmexg
    syl5eqel
    #
    cX
    cvv
    unisng
    syl
    uneq1d
    @0
    @4
    cX
    wss
    #
    @6
    cX
    wceq
    @0
    @3
    cX
    cpw
    #
    wss
    @9
    @0
    cA
    cB
    @10
    @0
    cA
    vx
    cX
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    wn
    #
    vy
    cX
    crab
    #
    cmpt
    #
    crn
    #
    @10
    ordtval.2
    @0
    cX
    @10
    @15
    wf
    @16
    @10
    wss
    @0
    vx
    cX
    @14
    @10
    @15
    @0
    @12
    cX
    wcel
    #
    wa
    #
    @14
    @10
    wcel
    #
    @14
    cX
    wss
    #
    @13
    vy
    cX
    ssrab2
    @18
    @7
    @19
    @20
    wb
    @0
    @7
    @17
    @8
    adantr
    #
    @14
    cX
    cvv
    elpw2g
    syl
    mpbiri
    @15
    eqid
    fmptd
    cX
    @10
    @15
    frn
    syl
    syl5eqss
    @0
    cB
    vx
    cX
    @12
    @11
    cR
    wbr
    wn
    #
    vy
    cX
    crab
    #
    cmpt
    #
    crn
    #
    @10
    ordtval.3
    @0
    cX
    @10
    @24
    wf
    @25
    @10
    wss
    @0
    vx
    cX
    @23
    @10
    @24
    @18
    @23
    @10
    wcel
    #
    @23
    cX
    wss
    #
    @22
    vy
    cX
    ssrab2
    @18
    @7
    @26
    @27
    wb
    @21
    @23
    cX
    cvv
    elpw2g
    syl
    mpbiri
    @24
    eqid
    fmptd
    cX
    @10
    @24
    frn
    syl
    syl5eqss
    unssd
    @3
    cX
    sspwuni
    sylib
    @4
    cX
    ssequn2
    sylib
    eqtr2d
    @1
    @3
    uniun
    syl6eqr
end
