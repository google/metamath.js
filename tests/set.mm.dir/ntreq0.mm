include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "ntrval.mm"
include "eqeq1d.mm"
include "wex.mm"
include "wrex.mm"
include "wn.mm"
include "neq0.mm"
include "con1bii.mm"
include "ancom.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"
include "exbii.mm"
include "eluni.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "rexcom4.mm"
include "19.42v.mm"
include "rexbii.mm"
include "3bitr2i.mm"
include "notbii.mm"
include "bitr3i.mm"
include "ralinexa.mm"
include "selpw.mm"
include "imbi12i.mm"
include "ralbii.mm"
include "syl6bb.mm"

theorem ntreq0
  let vx: setvar x
  let cS: class S
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J

  disjoint J x
  disjoint S x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint P x
  disjoint S y
  disjoint S z
  disjoint U x
  disjoint X y
  disjoint X z
  disjoint T x
  disjoint A x
  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( ( int ` J ) ` S ) = (/) <-> A. x e. J ( x C_ S -> x = (/) ) ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    #
    cS
    cJ
    cnt
    cfv
    cfv
    #
    c0
    wceq
    cJ
    cS
    cpw
    #
    cin
    #
    cuni
    #
    c0
    wceq
    #
    vx
    cv
    #
    cS
    wss
    #
    @6
    c0
    wceq
    #
    wi
    #
    vx
    cJ
    wral
    #
    @0
    @1
    @4
    c0
    cS
    cJ
    cX
    clscld.1
    ntrval
    eqeq1d
    @5
    @6
    @2
    wcel
    #
    vy
    cv
    #
    @6
    wcel
    #
    vy
    wex
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wn
    #
    @11
    @14
    wn
    #
    wi
    #
    vx
    cJ
    wral
    @10
    @5
    @12
    @4
    wcel
    #
    vy
    wex
    #
    wn
    @17
    @5
    @21
    vy
    @4
    neq0
    con1bii
    @21
    @16
    @21
    @11
    @13
    wa
    #
    vx
    cJ
    wrex
    #
    vy
    wex
    @22
    vy
    wex
    #
    vx
    cJ
    wrex
    @16
    @20
    @23
    vy
    @13
    @6
    @3
    wcel
    #
    wa
    #
    vx
    wex
    @6
    cJ
    wcel
    #
    @22
    wa
    #
    vx
    wex
    @20
    @23
    @26
    @28
    vx
    @26
    @25
    @13
    wa
    @27
    @11
    wa
    #
    @13
    wa
    @28
    @13
    @25
    ancom
    @25
    @29
    @13
    @6
    cJ
    @2
    elin
    anbi1i
    @27
    @11
    @13
    anass
    3bitri
    exbii
    vx
    @12
    @3
    eluni
    @22
    vx
    cJ
    df-rex
    3bitr4i
    exbii
    @22
    vx
    vy
    cJ
    rexcom4
    @24
    @15
    vx
    cJ
    @11
    @13
    vy
    19.42v
    rexbii
    3bitr2i
    notbii
    bitr3i
    @11
    @14
    vx
    cJ
    ralinexa
    @19
    @9
    vx
    cJ
    @11
    @7
    @18
    @8
    vx
    cS
    selpw
    @8
    @14
    vy
    @6
    neq0
    con1bii
    imbi12i
    ralbii
    3bitr2i
    syl6bb
end
