include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wel.mm"
include "wb.mm"
include "cvv.mm"
include "wf1.mm"
include "ct0.mm"
include "wa.mm"
include "kqfeq.mm"
include "3expb.mm"
include "imbi1d.mm"
include "2ralbidva.mm"
include "wf.mm"
include "wfn.mm"
include "kqffn.mm"
include "dffn2.mm"
include "sylib.mm"
include "dff13.mm"
include "baib.mm"
include "syl.mm"
include "ist0-2.mm"
include "3bitr4rd.mm"

theorem ist0-4
  let vx: setvar x
  let vy: setvar y
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
  let cU: class U
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
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Kol2 <-> F : X -1-1-> _V ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    vz
    cv
    #
    cF
    cfv
    vw
    cv
    #
    cF
    cfv
    wceq
    #
    @2
    @3
    wceq
    #
    wi
    #
    vw
    cX
    wral
    vz
    cX
    wral
    #
    vz
    vy
    wel
    vw
    vy
    wel
    wb
    vy
    cJ
    wral
    #
    @5
    wi
    #
    vw
    cX
    wral
    vz
    cX
    wral
    cX
    cvv
    cF
    wf1
    #
    cJ
    ct0
    wcel
    @1
    @6
    @9
    vz
    vw
    cX
    cX
    @1
    @2
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    wa
    wa
    @4
    @8
    @5
    @1
    @11
    @12
    @4
    @8
    wb
    vx
    vy
    @2
    @3
    cF
    cJ
    @0
    cX
    kqval.2
    kqfeq
    3expb
    imbi1d
    2ralbidva
    @1
    cX
    cvv
    cF
    wf
    #
    @10
    @7
    wb
    @1
    cF
    cX
    wfn
    @13
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    cX
    cF
    dffn2
    sylib
    @10
    @13
    @7
    vz
    vw
    cX
    cvv
    cF
    dff13
    baib
    syl
    vz
    vw
    vy
    cJ
    cX
    ist0-2
    3bitr4rd
end
