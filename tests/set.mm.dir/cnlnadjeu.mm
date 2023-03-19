include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wreu.mm"
include "ch0o.mm"
include "cif.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "reubidv.mm"
include "inss1.mm"
include "0lnop.mm"
include "0cnop.mm"
include "elin.mm"
include "mpbir2an.mm"
include "elimel.mm"
include "sselii.mm"
include "inss2.mm"
include "cnlnadjeui.mm"
include "dedth.mm"

theorem cnlnadjeu
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cT: class T

  disjoint t x
  disjoint t y
  disjoint T t
  disjoint x y
  disjoint T x
  disjoint T y
  assert |- ( T e. ( LinOp i^i ContOp ) -> E! t e. ( LinOp i^i ContOp ) A. x e. ~H A. y e. ~H ( ( T ` x ) .ih y ) = ( x .ih ( t ` y ) ) )

  proof
    cT
    clo
    ccop
    cin
    #
    wcel
    #
    vx
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    csp
    co
    #
    @2
    @4
    vt
    cv
    cfv
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    vt
    @0
    wreu
    @2
    @1
    cT
    ch0o
    cif
    #
    cfv
    #
    @4
    csp
    co
    #
    @6
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    vt
    @0
    wreu
    cT
    ch0o
    cT
    @9
    wceq
    #
    @8
    @13
    vt
    @0
    @14
    @7
    @12
    vx
    vy
    chil
    chil
    @14
    @5
    @11
    @6
    @14
    @3
    @10
    @4
    csp
    @2
    cT
    @9
    fveq1
    oveq1d
    eqeq1d
    2ralbidv
    reubidv
    vx
    vy
    vt
    @9
    @0
    clo
    @9
    clo
    ccop
    inss1
    cT
    ch0o
    @0
    ch0o
    @0
    wcel
    ch0o
    clo
    wcel
    ch0o
    ccop
    wcel
    0lnop
    0cnop
    ch0o
    clo
    ccop
    elin
    mpbir2an
    elimel
    #
    sselii
    @0
    ccop
    @9
    clo
    ccop
    inss2
    @15
    sselii
    cnlnadjeui
    dedth
end
