include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cima.mm"
include "wfn.mm"
include "wss.mm"
include "wi.mm"
include "kqffn.mm"
include "3ad2ant1.mm"
include "toponss.mm"
include "3adant3.mm"
include "fnfvima.mm"
include "3expia.mm"
include "syl2anc.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfun.mm"
include "fnfun.mm"
include "fvelima.mm"
include "ex.mm"
include "3syl.mm"
include "wa.mm"
include "wb.mm"
include "wral.mm"
include "simpl1.mm"
include "sselda.mm"
include "simpl3.mm"
include "kqfeq.mm"
include "syl3anc.mm"
include "eleq2.mm"
include "bibi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "simpl2.mm"
include "rspcv.mm"
include "syl.mm"
include "sylbid.mm"
include "simpr.mm"
include "biimp.mm"
include "syl6ci.mm"
include "rexlimdva.mm"
include "syld.mm"
include "impbid.mm"

theorem kqfvima
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
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
  disjoint A x
  disjoint A y
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
  disjoint y z
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
  assert |- ( ( J e. ( TopOn ` X ) /\ U e. J /\ A e. X ) -> ( A e. U <-> ( F ` A ) e. ( F " U ) ) )

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
    cA
    cX
    wcel
    #
    w3a
    #
    cA
    cU
    wcel
    #
    cA
    cF
    cfv
    #
    cF
    cU
    cima
    wcel
    #
    @4
    cF
    cX
    wfn
    #
    cU
    cX
    wss
    #
    @5
    @7
    wi
    @1
    @2
    @8
    @3
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    3ad2ant1
    #
    @1
    @2
    @9
    @3
    cU
    cJ
    cX
    toponss
    3adant3
    #
    @8
    @9
    @5
    @7
    cX
    cU
    cF
    cA
    fnfvima
    3expia
    syl2anc
    @4
    @7
    vz
    cv
    #
    cF
    cfv
    @6
    wceq
    #
    vz
    cU
    wrex
    #
    @5
    @4
    @8
    cF
    wfun
    #
    @7
    @14
    wi
    @10
    cX
    cF
    fnfun
    @15
    @7
    @14
    vz
    @6
    cU
    cF
    fvelima
    ex
    3syl
    @4
    @13
    @5
    vz
    cU
    @4
    @12
    cU
    wcel
    #
    wa
    #
    @13
    @16
    @5
    wb
    #
    @16
    @5
    @17
    @13
    @12
    vw
    cv
    #
    wcel
    #
    cA
    @19
    wcel
    #
    wb
    #
    vw
    cJ
    wral
    #
    @18
    @17
    @13
    @12
    vy
    cv
    #
    wcel
    #
    cA
    @24
    wcel
    #
    wb
    #
    vy
    cJ
    wral
    #
    @23
    @17
    @1
    @12
    cX
    wcel
    @3
    @13
    @28
    wb
    @1
    @2
    @3
    @16
    simpl1
    @4
    cU
    cX
    @12
    @11
    sselda
    @1
    @2
    @3
    @16
    simpl3
    vx
    vy
    @12
    cA
    cF
    cJ
    @0
    cX
    kqval.2
    kqfeq
    syl3anc
    @27
    @22
    vy
    vw
    cJ
    @24
    @19
    wceq
    @25
    @20
    @26
    @21
    @24
    @19
    @12
    eleq2
    @24
    @19
    cA
    eleq2
    bibi12d
    cbvralv
    syl6bb
    @17
    @2
    @23
    @18
    wi
    @1
    @2
    @3
    @16
    simpl2
    @22
    @18
    vw
    cU
    cJ
    @19
    cU
    wceq
    @20
    @16
    @21
    @5
    @19
    cU
    @12
    eleq2
    @19
    cU
    cA
    eleq2
    bibi12d
    rspcv
    syl
    sylbid
    @4
    @16
    simpr
    @16
    @5
    biimp
    syl6ci
    rexlimdva
    syld
    impbid
end
