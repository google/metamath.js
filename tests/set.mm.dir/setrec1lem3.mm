include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "exancom.mm"
include "ralbii.mm"
include "sylib.mm"
include "df-rex.mm"
include "sylibr.mm"
include "bnd2d.mm"
include "eluni.mm"
include "3bitr4i.mm"
include "dfss3.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "exbii.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "id.mm"
include "setrec1lem2.mm"
include "anim1i.mm"
include "ancomd.mm"
include "uniex.mm"
include "wceq.mm"
include "sseq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl.mm"
include "exlimiv.mm"

theorem setrec1lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cF: class F
  let cY: class Y
  let va: setvar a
  let vv: setvar v
  let vk: setvar k
  assume setrec1lem3.1: |- Y = { y | A. z ( A. w ( w C_ y -> ( w C_ z -> ( F ` w ) C_ z ) ) -> y C_ z ) }
  assume setrec1lem3.2: |- ( ph -> A e. _V )
  assume setrec1lem3.3: |- ( ph -> A. a e. A E. x ( a e. x /\ x e. Y ) )

  disjoint w y
  disjoint w z
  disjoint y z
  disjoint a x
  disjoint A a
  disjoint A x
  disjoint Y a
  disjoint Y x
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint a v
  disjoint v x
  disjoint A v
  disjoint Y v
  disjoint k x
  assert |- ( ph -> E. x ( A C_ x /\ x e. Y ) )

  proof
    wph
    vv
    cv
    #
    cY
    wss
    #
    cA
    @0
    cuni
    #
    wss
    #
    wa
    #
    vv
    wex
    #
    cA
    vx
    cv
    #
    wss
    #
    @6
    cY
    wcel
    #
    wa
    #
    vx
    wex
    #
    wph
    @1
    va
    cv
    #
    @6
    wcel
    #
    vx
    @0
    wrex
    #
    va
    cA
    wral
    #
    wa
    #
    vv
    wex
    @5
    wph
    @12
    va
    vx
    vv
    cA
    cY
    setrec1lem3.2
    wph
    @8
    @12
    wa
    vx
    wex
    #
    va
    cA
    wral
    #
    @12
    vx
    cY
    wrex
    #
    va
    cA
    wral
    wph
    @12
    @8
    wa
    vx
    wex
    #
    va
    cA
    wral
    @17
    setrec1lem3.3
    @19
    @16
    va
    cA
    @12
    @8
    vx
    exancom
    ralbii
    sylib
    @18
    @16
    va
    cA
    @12
    vx
    cY
    df-rex
    ralbii
    sylibr
    bnd2d
    @15
    @4
    vv
    @14
    @3
    @1
    @14
    @11
    @2
    wcel
    #
    va
    cA
    wral
    @3
    @13
    @20
    va
    cA
    @6
    @0
    wcel
    #
    @12
    wa
    vx
    wex
    @12
    @21
    wa
    vx
    wex
    @13
    @20
    @21
    @12
    vx
    exancom
    @12
    vx
    @0
    df-rex
    vx
    @11
    @0
    eluni
    3bitr4i
    ralbii
    va
    cA
    @2
    dfss3
    bitr4i
    anbi2i
    exbii
    sylib
    @4
    @10
    vv
    @4
    @3
    @2
    cY
    wcel
    #
    wa
    #
    @10
    @4
    @22
    @3
    @1
    @22
    @3
    @1
    vy
    vz
    vw
    cF
    cvv
    @0
    cY
    setrec1lem3.1
    @0
    cvv
    wcel
    @1
    vv
    vex
    #
    a1i
    @1
    id
    setrec1lem2
    anim1i
    ancomd
    @9
    @23
    vx
    @2
    @0
    @24
    uniex
    @6
    @2
    wceq
    @7
    @3
    @8
    @22
    @6
    @2
    cA
    sseq2
    @6
    @2
    cY
    eleq1
    anbi12d
    spcev
    syl
    exlimiv
    syl
end
