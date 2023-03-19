include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "crn.mm"
include "cfn.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "cmbf.mm"
include "w3a.mm"
include "isi1f.mm"
include "simprbi.mm"
include "simp1d.mm"

theorem i1ff
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( F e. dom S.1 -> F : RR --> RR )

  proof
    cF
    citg1
    cdm
    wcel
    #
    cr
    cr
    cF
    wf
    #
    cF
    crn
    cfn
    wcel
    #
    cF
    ccnv
    cr
    cc0
    csn
    cdif
    cima
    cvol
    cfv
    cr
    wcel
    #
    @0
    cF
    cmbf
    wcel
    @1
    @2
    @3
    w3a
    cF
    isi1f
    simprbi
    simp1d
end
