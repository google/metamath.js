include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "jca.mm"
include "rgen2a.mm"
include "cvv.mm"
include "ismet.mm"
include "ax-mp.mm"
include "mpbir2an.mm"

theorem ismeti
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cX: class X
  assume ismeti.0: |- X e. _V
  assume ismeti.1: |- D : ( X X. X ) --> RR
  assume ismeti.2: |- ( ( x e. X /\ y e. X ) -> ( ( x D y ) = 0 <-> x = y ) )
  assume ismeti.3: |- ( ( x e. X /\ y e. X /\ z e. X ) -> ( x D y ) <_ ( ( z D x ) + ( z D y ) ) )

  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- D e. ( Met ` X )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cX
    cX
    cxp
    cr
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
    caddc
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
    ismeti.1
    @9
    vx
    vy
    cX
    @2
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    wa
    #
    @5
    @8
    ismeti.2
    @13
    @7
    vz
    cX
    @11
    @12
    @6
    cX
    wcel
    @7
    ismeti.3
    3expa
    ralrimiva
    jca
    rgen2a
    cX
    cvv
    wcel
    @0
    @1
    @10
    wa
    wb
    ismeti.0
    vx
    vy
    vz
    cvv
    cD
    cX
    ismet
    ax-mp
    mpbir2an
end
