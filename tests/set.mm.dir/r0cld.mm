include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckq.mm"
include "ct1.mm"
include "w3a.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "crab.mm"
include "ccld.mm"
include "wfn.mm"
include "wceq.mm"
include "kqffn.mm"
include "3ad2ant1.mm"
include "fncnvima2.mm"
include "syl.mm"
include "wa.mm"
include "fvex.mm"
include "elsn.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl3.mm"
include "kqfeq.mm"
include "eleq2.mm"
include "bibi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "syl3anc.mm"
include "syl5bb.mm"
include "rabbidva.mm"
include "eqtrd.mm"
include "ccn.mm"
include "co.mm"
include "kqid.mm"
include "cuni.mm"
include "simp2.mm"
include "crn.mm"
include "simp3.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "kqtopon.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "t1sncld.mm"
include "cnclima.mm"
include "eqeltrrd.mm"

theorem r0cld
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cU: class U
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J o
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint F o
  disjoint F z
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint X z
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
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
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
  disjoint F a
  disjoint F b
  disjoint F m
  disjoint F n
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint U w
  disjoint U z
  disjoint V x
  assert |- ( ( J e. ( TopOn ` X ) /\ ( KQ ` J ) e. Fre /\ A e. X ) -> { z e. X | A. o e. J ( z e. o <-> A e. o ) } e. ( Clsd ` J ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    ckq
    cfv
    #
    ct1
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cF
    ccnv
    cA
    cF
    cfv
    #
    csn
    #
    cima
    #
    vz
    cv
    #
    vo
    cv
    #
    wcel
    #
    cA
    @10
    wcel
    #
    wb
    #
    vo
    cJ
    wral
    #
    vz
    cX
    crab
    #
    cJ
    ccld
    cfv
    #
    @5
    @8
    @9
    cF
    cfv
    #
    @7
    wcel
    #
    vz
    cX
    crab
    #
    @15
    @5
    cF
    cX
    wfn
    #
    @8
    @19
    wceq
    @1
    @3
    @20
    @4
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
    vz
    cX
    @7
    cF
    fncnvima2
    syl
    @5
    @18
    @14
    vz
    cX
    @18
    @17
    @6
    wceq
    #
    @5
    @9
    cX
    wcel
    #
    wa
    #
    @14
    @17
    @6
    @9
    cF
    fvex
    elsn
    @24
    @1
    @23
    @4
    @22
    @14
    wb
    @1
    @3
    @4
    @23
    simpl1
    @5
    @23
    simpr
    @1
    @3
    @4
    @23
    simpl3
    @1
    @23
    @4
    w3a
    @22
    @9
    vy
    cv
    #
    wcel
    #
    cA
    @25
    wcel
    #
    wb
    #
    vy
    cJ
    wral
    @14
    vx
    vy
    @9
    cA
    cF
    cJ
    @0
    cX
    kqval.2
    kqfeq
    @28
    @13
    vy
    vo
    cJ
    @25
    @10
    wceq
    @26
    @11
    @27
    @12
    @25
    @10
    @9
    eleq2
    @25
    @10
    cA
    eleq2
    bibi12d
    cbvralv
    syl6bb
    syl3anc
    syl5bb
    rabbidva
    eqtrd
    @5
    cF
    cJ
    @2
    ccn
    co
    wcel
    #
    @7
    @2
    ccld
    cfv
    wcel
    #
    @8
    @16
    wcel
    @1
    @3
    @29
    @4
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqid
    3ad2ant1
    @5
    @3
    @6
    @2
    cuni
    #
    wcel
    @30
    @1
    @3
    @4
    simp2
    @5
    @6
    cF
    crn
    #
    @31
    @5
    @20
    @4
    @6
    @32
    wcel
    @21
    @1
    @3
    @4
    simp3
    cX
    cA
    cF
    fnfvelrn
    syl2anc
    @5
    @2
    @32
    ctopon
    cfv
    wcel
    #
    @32
    @31
    wceq
    @1
    @3
    @33
    @4
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    3ad2ant1
    @32
    @2
    toponuni
    syl
    eleqtrd
    @6
    @2
    @31
    @31
    eqid
    t1sncld
    syl2anc
    @7
    cF
    cJ
    @2
    cnclima
    syl2anc
    eqeltrrd
end
