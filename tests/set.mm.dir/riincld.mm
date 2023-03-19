include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "ciin.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "riin0.mm"
include "adantl.mm"
include "topcld.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "simpr.mm"
include "simplr.mm"
include "iincld.mm"
include "syl2anc.mm"
include "incld.mm"
include "pm2.61dane.mm"

theorem riincld
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cU: class U
  let cT: class T
  assume clscld.1: |- X = U. J

  disjoint J x
  disjoint X x
  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint P x
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U x
  disjoint X y
  disjoint X z
  disjoint T x
  assert |- ( ( J e. Top /\ A. x e. A B e. ( Clsd ` J ) ) -> ( X i^i |^|_ x e. A B ) e. ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cB
    cJ
    ccld
    cfv
    #
    wcel
    vx
    cA
    wral
    #
    wa
    #
    cX
    vx
    cA
    cB
    ciin
    #
    cin
    #
    @1
    wcel
    #
    cA
    c0
    @3
    cA
    c0
    wceq
    #
    wa
    @5
    cX
    @1
    @7
    @5
    cX
    wceq
    @3
    vx
    cX
    cB
    cA
    riin0
    adantl
    @0
    cX
    @1
    wcel
    #
    @2
    @7
    cJ
    cX
    clscld.1
    topcld
    #
    ad2antrr
    eqeltrd
    @3
    cA
    c0
    wne
    #
    wa
    #
    @8
    @4
    @1
    wcel
    #
    @6
    @0
    @8
    @2
    @10
    @9
    ad2antrr
    @11
    @10
    @2
    @12
    @3
    @10
    simpr
    @0
    @2
    @10
    simplr
    vx
    cA
    cB
    cJ
    iincld
    syl2anc
    cX
    @4
    cJ
    incld
    syl2anc
    pm2.61dane
end
