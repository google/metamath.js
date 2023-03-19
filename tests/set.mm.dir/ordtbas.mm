include "ctsr.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "w3o.mm"
include "cvv.mm"
include "wb.mm"
include "snex.mm"
include "wss.mm"
include "ssun2.mm"
include "cuni.mm"
include "ordtuni.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "ssexg.mm"
include "sylancr.mm"
include "elfiun.mm"
include "wi.mm"
include "fisn.mm"
include "ssun1.mm"
include "eqsstri.mm"
include "sseli.mm"
include "a1i.mm"
include "ordtbas2.mm"
include "syl6eqss.mm"
include "sseld.mm"
include "wa.mm"
include "cpw.mm"
include "fipwuni.mm"
include "elpwid.mm"
include "ad2antll.mm"
include "unissi.mm"
include "syl5sseqr.mm"
include "adantr.mm"
include "sstrd.mm"
include "simprl.mm"
include "syl6eleq.mm"
include "elsni.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "sselda.mm"
include "adantrl.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "3jaod.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ssfii.mm"
include "unssad.mm"
include "fiss.mm"
include "sylancl.mm"
include "eqsstr3d.mm"
include "unssd.mm"
include "eqssd.mm"
include "unass.mm"
include "syl6eqr.mm"

theorem ordtbas
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cV: class V
  assume ordtval.1: |- X = dom R
  assume ordtval.2: |- A = ran ( x e. X |-> { y e. X | -. y R x } )
  assume ordtval.3: |- B = ran ( x e. X |-> { y e. X | -. x R y } )
  assume ordtval.4: |- C = ran ( a e. X , b e. X |-> { y e. X | ( -. y R a /\ -. b R y ) } )

  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a x
  disjoint a y
  disjoint R a
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X a
  disjoint X b
  disjoint X x
  disjoint X y
  disjoint B a
  disjoint B b
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a w
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b w
  disjoint b z
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
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X w
  disjoint X z
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B z
  disjoint C m
  disjoint C n
  disjoint C z
  disjoint V x
  assert |- ( R e. TosetRel -> ( fi ` ( { X } u. ( A u. B ) ) ) = ( ( { X } u. ( A u. B ) ) u. C ) )

  proof
    cR
    ctsr
    wcel
    #
    cX
    csn
    #
    cA
    cB
    cun
    #
    cun
    #
    cfi
    cfv
    #
    @1
    @2
    cC
    cun
    #
    cun
    #
    @3
    cC
    cun
    @0
    @4
    @6
    @0
    vz
    @4
    @6
    @0
    vz
    cv
    #
    @4
    wcel
    #
    @7
    @1
    cfi
    cfv
    #
    wcel
    #
    @7
    @2
    cfi
    cfv
    #
    wcel
    #
    @7
    vm
    cv
    #
    vn
    cv
    #
    cin
    #
    wceq
    #
    vn
    @11
    wrex
    vm
    @9
    wrex
    #
    w3o
    #
    @7
    @6
    wcel
    #
    @0
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    #
    @8
    @18
    wb
    cX
    snex
    @0
    @2
    @3
    wss
    #
    @3
    cvv
    wcel
    #
    @20
    @2
    @1
    ssun2
    #
    @0
    @3
    cuni
    #
    cvv
    wcel
    @22
    @0
    cX
    @24
    cvv
    vx
    vy
    cA
    cB
    cR
    ctsr
    cX
    ordtval.1
    ordtval.2
    ordtval.3
    ordtuni
    #
    @0
    cX
    cR
    cdm
    cvv
    ordtval.1
    cR
    ctsr
    dmexg
    syl5eqel
    eqeltrrd
    @3
    uniexb
    sylibr
    #
    @2
    @3
    cvv
    ssexg
    sylancr
    vm
    vn
    @7
    @1
    @2
    cvv
    cvv
    elfiun
    sylancr
    @0
    @10
    @19
    @12
    @17
    @10
    @19
    wi
    @0
    @9
    @6
    @7
    @9
    @1
    @6
    cX
    fisn
    #
    @1
    @5
    ssun1
    eqsstri
    sseli
    a1i
    @0
    @11
    @6
    @7
    @0
    @11
    @5
    @6
    vx
    vy
    cA
    cB
    cC
    cR
    cX
    va
    vb
    ordtval.1
    ordtval.2
    ordtval.3
    ordtval.4
    ordtbas2
    #
    @5
    @1
    ssun2
    syl6eqss
    #
    sseld
    @0
    @16
    @19
    vm
    vn
    @9
    @11
    @0
    @13
    @9
    wcel
    #
    @14
    @11
    wcel
    #
    wa
    #
    wa
    #
    @19
    @16
    @15
    @6
    wcel
    @33
    @15
    @14
    @6
    @33
    @14
    @13
    wss
    @15
    @14
    wceq
    @33
    @14
    cX
    @13
    @33
    @14
    @2
    cuni
    #
    cX
    @31
    @14
    @34
    wss
    @0
    @30
    @31
    @14
    @34
    @11
    @34
    cpw
    @14
    @2
    fipwuni
    sseli
    elpwid
    ad2antll
    @0
    @34
    cX
    wss
    @32
    @0
    @24
    @34
    cX
    @2
    @3
    @23
    unissi
    @25
    syl5sseqr
    adantr
    sstrd
    @33
    @13
    @1
    wcel
    @13
    cX
    wceq
    @33
    @13
    @9
    @1
    @0
    @30
    @31
    simprl
    @27
    syl6eleq
    @13
    cX
    elsni
    syl
    sseqtr4d
    @14
    @13
    sseqin2
    sylib
    @0
    @31
    @14
    @6
    wcel
    @30
    @0
    @11
    @6
    @14
    @29
    sselda
    adantrl
    eqeltrd
    @7
    @15
    @6
    eleq1
    syl5ibrcom
    rexlimdvva
    3jaod
    sylbid
    ssrdv
    @0
    @1
    @5
    @4
    @0
    @1
    @2
    @4
    @0
    @22
    @3
    @4
    wss
    @26
    @3
    cvv
    ssfii
    syl
    unssad
    @0
    @5
    @11
    @4
    @28
    @0
    @22
    @21
    @11
    @4
    wss
    @26
    @23
    @2
    @3
    cvv
    fiss
    sylancl
    eqsstr3d
    unssd
    eqssd
    @1
    @2
    cC
    unass
    syl6eqr
end
