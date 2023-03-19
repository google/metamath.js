include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cxrs.mm"
include "cds.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "cr.mm"
include "wceq.mm"
include "metcl.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "eqid.mm"
include "xrsdsreval.mm"
include "syl2anc.mm"
include "cxmt.mm"
include "wbr.mm"
include "metxmet.mm"
include "xmetrtri2.mm"
include "sylan.mm"
include "eqbrtrrd.mm"

theorem metrtri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R


  assert |- ( ( D e. ( Met ` X ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( abs ` ( ( A D C ) - ( B D C ) ) ) <_ ( A D B ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cC
    cD
    co
    #
    cB
    cC
    cD
    co
    #
    cxrs
    cds
    cfv
    #
    co
    #
    @6
    @7
    cmin
    co
    cabs
    cfv
    #
    cA
    cB
    cD
    co
    #
    cle
    @5
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @9
    @10
    wceq
    @0
    @1
    @3
    @12
    @2
    cA
    cC
    cD
    cX
    metcl
    3adant3r2
    @0
    @2
    @3
    @13
    @1
    cB
    cC
    cD
    cX
    metcl
    3adant3r1
    @6
    @7
    @8
    @8
    eqid
    #
    xrsdsreval
    syl2anc
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    @4
    @9
    @11
    cle
    wbr
    cD
    cX
    metxmet
    cA
    cB
    cC
    cD
    @8
    cX
    @14
    xmetrtri2
    sylan
    eqbrtrrd
end
