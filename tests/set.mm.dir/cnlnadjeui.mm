include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "wreu.mm"
include "wrex.mm"
include "wrmo.mm"
include "cnlnadji.mm"
include "wf.mm"
include "wa.mm"
include "wmo.mm"
include "adjmo.mm"
include "wcel.mm"
include "inss1.mm"
include "sseli.mm"
include "lnopf.mm"
include "syl.mm"
include "simpl.mm"
include "eqcom.mm"
include "2ralbii.mm"
include "wb.mm"
include "lnopfi.mm"
include "adjsym.mm"
include "mpan2.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "jca.mm"
include "sylan.mm"
include "moimi.mm"
include "df-rmo.mm"
include "sylibr.mm"
include "ax-mp.mm"
include "reu5.mm"
include "mpbir2an.mm"

theorem cnlnadjeui
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume cnlnadj.1: |- T e. LinOp
  assume cnlnadj.2: |- T e. ContOp

  disjoint t x
  disjoint t y
  disjoint T t
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint f g
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint T f
  disjoint g t
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint T g
  disjoint t v
  disjoint t w
  disjoint t z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- E! t e. ( LinOp i^i ContOp ) A. x e. ~H A. y e. ~H ( ( T ` x ) .ih y ) = ( x .ih ( t ` y ) )

  proof
    vx
    cv
    #
    cT
    cfv
    vy
    cv
    #
    csp
    co
    #
    @0
    @1
    vt
    cv
    #
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
    clo
    ccop
    cin
    #
    wreu
    @6
    vt
    @7
    wrex
    @6
    vt
    @7
    wrmo
    #
    vx
    vy
    vt
    cT
    cnlnadj.1
    cnlnadj.2
    cnlnadji
    chil
    chil
    @3
    wf
    #
    @0
    @1
    cT
    cfv
    csp
    co
    @0
    @3
    cfv
    @1
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    #
    wa
    #
    vt
    wmo
    #
    @8
    vx
    vy
    vt
    cT
    adjmo
    @12
    @3
    @7
    wcel
    #
    @6
    wa
    #
    vt
    wmo
    @8
    @14
    @11
    vt
    @13
    @9
    @6
    @11
    @13
    @3
    clo
    wcel
    @9
    @7
    clo
    @3
    clo
    ccop
    inss1
    sseli
    @3
    lnopf
    syl
    @9
    @6
    wa
    @9
    @10
    @9
    @6
    simpl
    @9
    @6
    @10
    @6
    @4
    @2
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @9
    @10
    @5
    @15
    vx
    vy
    chil
    chil
    @2
    @4
    eqcom
    2ralbii
    @9
    chil
    chil
    cT
    wf
    @16
    @10
    wb
    cT
    cnlnadj.1
    lnopfi
    vx
    vy
    @3
    cT
    adjsym
    mpan2
    syl5bb
    biimpa
    jca
    sylan
    moimi
    @6
    vt
    @7
    df-rmo
    sylibr
    ax-mp
    @6
    vt
    @7
    reu5
    mpbir2an
end
