include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "wb.mm"
include "wfn.mm"
include "kqffn.mm"
include "elpreima.mm"
include "syl.mm"
include "adantr.mm"
include "kqfvima.mm"
include "3expa.mm"
include "biimprd.mm"
include "expimpd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "cdm.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "toponss.mm"
include "fndm.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "dminss.mm"
include "syl6eqssr.mm"
include "eqssd.mm"

theorem kqsat
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint m n
  disjoint m o
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n o
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b o
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m u
  disjoint m v
  disjoint J m
  disjoint n u
  disjoint n v
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint J o
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint F a
  disjoint F b
  disjoint F m
  disjoint F n
  disjoint F o
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint U w
  disjoint U z
  disjoint V x
  assert |- ( ( J e. ( TopOn ` X ) /\ U e. J ) -> ( `' F " ( F " U ) ) = U )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cU
    cJ
    wcel
    #
    wa
    #
    cF
    ccnv
    cF
    cU
    cima
    #
    cima
    #
    cU
    @3
    vz
    @5
    cU
    @3
    vz
    cv
    #
    @5
    wcel
    #
    @6
    cX
    wcel
    #
    @6
    cF
    cfv
    @4
    wcel
    #
    wa
    #
    @6
    cU
    wcel
    #
    @1
    @7
    @10
    wb
    #
    @2
    @1
    cF
    cX
    wfn
    #
    @12
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    #
    cX
    @6
    @4
    cF
    elpreima
    syl
    adantr
    @3
    @8
    @9
    @11
    @3
    @8
    wa
    @11
    @9
    @1
    @2
    @8
    @11
    @9
    wb
    vx
    vy
    @6
    cU
    cF
    cJ
    cX
    kqval.2
    kqfvima
    3expa
    biimprd
    expimpd
    sylbid
    ssrdv
    @3
    cU
    cF
    cdm
    #
    cU
    cin
    #
    @5
    @3
    cU
    @15
    wss
    @16
    cU
    wceq
    @3
    cU
    cX
    @15
    cU
    cJ
    cX
    toponss
    @1
    @15
    cX
    wceq
    #
    @2
    @1
    @13
    @17
    @14
    cX
    cF
    fndm
    syl
    adantr
    sseqtr4d
    cU
    @15
    sseqin2
    sylib
    cU
    cF
    dminss
    syl6eqssr
    eqssd
end
