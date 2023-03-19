include "cho.mm"
include "wcel.mm"
include "cei.mm"
include "cfv.mm"
include "wa.mm"
include "chil.mm"
include "cel.mm"
include "cc.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "c0v.mm"
include "wne.mm"
include "csp.mm"
include "cr.mm"
include "wf.mm"
include "hmopf.mm"
include "eleigveccl.mm"
include "eigvalcl.mm"
include "jca.mm"
include "eigvec1.mm"
include "sylan.mm"
include "hmop.mm"
include "3expb.mm"
include "syldan.mm"
include "eigre.mm"
include "biimpa.mm"
include "syl2anc.mm"

theorem eighmre
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T e. HrmOp /\ A e. ( eigvec ` T ) ) -> ( ( eigval ` T ) ` A ) e. RR )

  proof
    cT
    cho
    wcel
    #
    cA
    cT
    cei
    cfv
    wcel
    #
    wa
    cA
    chil
    wcel
    #
    cA
    cT
    cel
    cfv
    cfv
    #
    cc
    wcel
    #
    wa
    #
    cA
    cT
    cfv
    #
    @3
    cA
    csm
    co
    wceq
    cA
    c0v
    wne
    wa
    #
    wa
    #
    cA
    @6
    csp
    co
    @6
    cA
    csp
    co
    wceq
    #
    @3
    cr
    wcel
    #
    @0
    chil
    chil
    cT
    wf
    #
    @1
    @8
    cT
    hmopf
    #
    @11
    @1
    wa
    #
    @5
    @7
    @13
    @2
    @4
    cA
    cT
    eleigveccl
    #
    cA
    cT
    eigvalcl
    jca
    cA
    cT
    eigvec1
    jca
    sylan
    @0
    @1
    @2
    @2
    wa
    #
    @9
    @0
    @11
    @1
    @15
    @12
    @13
    @2
    @2
    @14
    @14
    jca
    sylan
    @0
    @2
    @2
    @9
    cA
    cA
    cT
    hmop
    3expb
    syldan
    @8
    @9
    @10
    cA
    @3
    cT
    eigre
    biimpa
    syl2anc
end
