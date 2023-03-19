include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wa.mm"
include "cpt.mm"
include "cfv.mm"
include "cv.mm"
include "wfn.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wex.mm"
include "cab.mm"
include "ctg.mm"
include "ffn.mm"
include "eqid.mm"
include "ptval.mm"
include "sylan2.mm"
include "ctb.mm"
include "ptbas.mm"
include "tgcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem pttop
  let cA: class A
  let cF: class F
  let cV: class V
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. V /\ F : A --> Top ) -> ( Xt_ ` F ) e. Top )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    wa
    #
    cF
    cpt
    cfv
    #
    vg
    cv
    #
    cA
    wfn
    vy
    cv
    #
    @4
    cfv
    #
    @5
    cF
    cfv
    #
    wcel
    vy
    cA
    wral
    @6
    @7
    cuni
    wceq
    vy
    cA
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    w3a
    vx
    cv
    vy
    cA
    @6
    cixp
    wceq
    wa
    vg
    wex
    vx
    cab
    #
    ctg
    cfv
    #
    ctop
    @1
    @0
    cF
    cA
    wfn
    @3
    @9
    wceq
    cA
    ctop
    cF
    ffn
    vx
    vy
    vz
    cA
    @8
    vg
    cF
    cV
    @8
    eqid
    #
    ptval
    sylan2
    @2
    @8
    ctb
    wcel
    @9
    ctop
    wcel
    vx
    vy
    vz
    cA
    @8
    vg
    cF
    cV
    @10
    ptbas
    @8
    tgcl
    syl
    eqeltrd
end
