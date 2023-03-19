include "ctop.mm"
include "wcel.mm"
include "cfn.mm"
include "ccld.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "cdif.mm"
include "ciin.mm"
include "cin.mm"
include "ciun.mm"
include "difin.mm"
include "iundif2.mm"
include "eqtr4i.mm"
include "wceq.mm"
include "wss.mm"
include "cldss.mm"
include "dfss4.mm"
include "sylib.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "iuneq2.mm"
include "syl.mm"
include "syl5eq.mm"
include "simp1.mm"
include "cldopn.mm"
include "riinopn.mm"
include "syl3an3.mm"
include "opncld.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem iuncld
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
  assert |- ( ( J e. Top /\ A e. Fin /\ A. x e. A B e. ( Clsd ` J ) ) -> U_ x e. A B e. ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cfn
    wcel
    #
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    vx
    cA
    wral
    #
    w3a
    #
    cX
    cX
    vx
    cA
    cX
    cB
    cdif
    #
    ciin
    #
    cin
    #
    cdif
    #
    vx
    cA
    cB
    ciun
    #
    @2
    @5
    @9
    vx
    cA
    cX
    @6
    cdif
    #
    ciun
    #
    @10
    @9
    cX
    @7
    cdif
    @12
    cX
    @7
    difin
    vx
    cA
    cX
    @6
    iundif2
    eqtr4i
    @5
    @11
    cB
    wceq
    #
    vx
    cA
    wral
    #
    @12
    @10
    wceq
    @4
    @0
    @14
    @1
    @3
    @13
    vx
    cA
    @3
    cB
    cX
    wss
    @13
    cB
    cJ
    cX
    clscld.1
    cldss
    cB
    cX
    dfss4
    sylib
    ralimi
    3ad2ant3
    vx
    cA
    @11
    cB
    iuneq2
    syl
    syl5eq
    @5
    @0
    @8
    cJ
    wcel
    #
    @9
    @2
    wcel
    @0
    @1
    @4
    simp1
    @4
    @0
    @1
    @6
    cJ
    wcel
    #
    vx
    cA
    wral
    @15
    @3
    @16
    vx
    cA
    cB
    cJ
    cX
    clscld.1
    cldopn
    ralimi
    vx
    cA
    @6
    cJ
    cX
    clscld.1
    riinopn
    syl3an3
    @8
    cJ
    cX
    clscld.1
    opncld
    syl2anc
    eqeltrrd
end
