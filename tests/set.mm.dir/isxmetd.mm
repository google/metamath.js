include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "3exp2.mm"
include "imp32.mm"
include "ralrimiv.mm"
include "jca.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "isxmet.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem isxmetd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cX: class X
  assume isxmetd.0: |- ( ph -> X e. _V )
  assume isxmetd.1: |- ( ph -> D : ( X X. X ) --> RR* )
  assume isxmetd.2: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( ( x D y ) = 0 <-> x = y ) )
  assume isxmetd.3: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( x D y ) <_ ( ( z D x ) +e ( z D y ) ) )

  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> D e. ( *Met ` X ) )

  proof
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    cc0
    wceq
    @2
    @3
    wceq
    wb
    #
    @4
    vz
    cv
    #
    @2
    cD
    co
    @6
    @3
    cD
    co
    cxad
    co
    cle
    wbr
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    isxmetd.1
    wph
    @9
    vx
    vy
    cX
    cX
    wph
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
    #
    @5
    @8
    isxmetd.2
    @13
    @7
    vz
    cX
    wph
    @11
    @12
    @6
    cX
    wcel
    #
    @7
    wi
    wph
    @11
    @12
    @14
    @7
    isxmetd.3
    3exp2
    imp32
    ralrimiv
    jca
    ralrimivva
    wph
    cX
    cvv
    wcel
    @0
    @1
    @10
    wa
    wb
    isxmetd.0
    vx
    vy
    vz
    cvv
    cD
    cX
    isxmet
    syl
    mpbir2and
end
