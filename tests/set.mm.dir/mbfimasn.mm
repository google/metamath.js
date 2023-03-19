include "cmbf.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "w3a.mm"
include "ccnv.mm"
include "cicc.mm"
include "co.mm"
include "cima.mm"
include "csn.mm"
include "cvol.mm"
include "cdm.mm"
include "cxr.mm"
include "wceq.mm"
include "simp3.mm"
include "rexr.mm"
include "iccid.mm"
include "3syl.mm"
include "imaeq2d.mm"
include "wa.mm"
include "mbfimaicc.mm"
include "anabsan2.mm"
include "3impa.mm"
include "eqeltrrd.mm"

theorem mbfimasn
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( F e. MblFn /\ F : A --> RR /\ B e. RR ) -> ( `' F " { B } ) e. dom vol )

  proof
    cF
    cmbf
    wcel
    #
    cA
    cr
    cF
    wf
    #
    cB
    cr
    wcel
    #
    w3a
    #
    cF
    ccnv
    #
    cB
    cB
    cicc
    co
    #
    cima
    #
    @4
    cB
    csn
    #
    cima
    cvol
    cdm
    #
    @3
    @5
    @7
    @4
    @3
    @2
    cB
    cxr
    wcel
    @5
    @7
    wceq
    @0
    @1
    @2
    simp3
    cB
    rexr
    cB
    iccid
    3syl
    imaeq2d
    @0
    @1
    @2
    @6
    @8
    wcel
    #
    @0
    @1
    wa
    @2
    @9
    cA
    cB
    cB
    cF
    mbfimaicc
    anabsan2
    3impa
    eqeltrrd
end
