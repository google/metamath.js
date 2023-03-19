include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "adjcl.mm"
include "wb.mm"
include "eqcom.mm"
include "adj2.mm"
include "3com23.mm"
include "3expa.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "ralbidva.mm"
include "adantr.mm"
include "simpr.mm"
include "hial2eq2.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "riota5.mm"
include "eqcomd.mm"

theorem adjvalval
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cT: class T
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S

  disjoint w x
  disjoint A w
  disjoint A x
  disjoint T x
  disjoint T w
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T y
  disjoint T z
  assert |- ( ( T e. dom adjh /\ A e. ~H ) -> ( ( adjh ` T ) ` A ) = ( iota_ w e. ~H A. x e. ~H ( ( T ` x ) .ih A ) = ( x .ih w ) ) )

  proof
    cT
    cado
    cdm
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    vx
    cv
    #
    cT
    cfv
    cA
    csp
    co
    #
    @3
    vw
    cv
    #
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    vw
    chil
    crio
    cA
    cT
    cado
    cfv
    cfv
    #
    @2
    @8
    vw
    chil
    @9
    cA
    cT
    adjcl
    #
    @2
    @5
    chil
    wcel
    #
    wa
    #
    @8
    @6
    @3
    @9
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    @5
    @9
    wceq
    #
    @2
    @8
    @15
    wb
    @11
    @2
    @7
    @14
    vx
    chil
    @7
    @6
    @4
    wceq
    @2
    @3
    chil
    wcel
    #
    wa
    #
    @14
    @4
    @6
    eqcom
    @18
    @4
    @13
    @6
    @0
    @1
    @17
    @4
    @13
    wceq
    #
    @0
    @17
    @1
    @19
    @3
    cA
    cT
    adj2
    3com23
    3expa
    eqeq2d
    syl5bb
    ralbidva
    adantr
    @12
    @11
    @9
    chil
    wcel
    #
    @15
    @16
    wb
    @2
    @11
    simpr
    @2
    @20
    @11
    @10
    adantr
    vx
    @5
    @9
    hial2eq2
    syl2anc
    bitrd
    riota5
    eqcomd
end
