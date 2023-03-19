include "cc.mm"
include "wcel.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "wa.mm"
include "ccj.mm"
include "cfv.mm"
include "cbr.mm"
include "ccnv.mm"
include "csm.mm"
include "co.mm"
include "chft.mm"
include "chil.mm"
include "wceq.mm"
include "cnvbracl.mm"
include "cjcl.mm"
include "brafnmul.mm"
include "sylan.mm"
include "cjcj.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "sylan2.mm"
include "bracnvbra.mm"
include "oveq2d.mm"
include "adantl.mm"
include "fveq2d.mm"
include "hvmulcl.mm"
include "syl2an.mm"
include "cnvbrabra.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem cnvbramul
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U


  assert |- ( ( A e. CC /\ T e. ( LinFn i^i ContFn ) ) -> ( `' bra ` ( A .fn T ) ) = ( ( * ` A ) .h ( `' bra ` T ) ) )

  proof
    cA
    cc
    wcel
    #
    cT
    clf
    ccnfn
    cin
    wcel
    #
    wa
    #
    cA
    ccj
    cfv
    #
    cT
    cbr
    ccnv
    #
    cfv
    #
    csm
    co
    #
    cbr
    cfv
    #
    @4
    cfv
    #
    cA
    cT
    chft
    co
    #
    @4
    cfv
    @6
    @2
    @7
    @9
    @4
    @2
    @7
    cA
    @5
    cbr
    cfv
    #
    chft
    co
    #
    @9
    @1
    @0
    @5
    chil
    wcel
    #
    @7
    @11
    wceq
    cT
    cnvbracl
    #
    @0
    @12
    wa
    #
    @7
    @3
    ccj
    cfv
    #
    @10
    chft
    co
    #
    @11
    @0
    @3
    cc
    wcel
    #
    @12
    @7
    @16
    wceq
    cA
    cjcl
    #
    @3
    @5
    brafnmul
    sylan
    @14
    @15
    cA
    @10
    chft
    @0
    @15
    cA
    wceq
    @12
    cA
    cjcj
    adantr
    oveq1d
    eqtrd
    sylan2
    @1
    @11
    @9
    wceq
    @0
    @1
    @10
    cT
    cA
    chft
    cT
    bracnvbra
    oveq2d
    adantl
    eqtrd
    fveq2d
    @2
    @6
    chil
    wcel
    #
    @8
    @6
    wceq
    @0
    @17
    @12
    @19
    @1
    @18
    @13
    @3
    @5
    hvmulcl
    syl2an
    @6
    cnvbrabra
    syl
    eqtr3d
end
