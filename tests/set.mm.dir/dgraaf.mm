include "caa.mm"
include "cn.mm"
include "cdgraa.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cdgr.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cq.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "ltso.mm"
include "infex.mm"
include "df-dgraa.mm"
include "fnmpti.mm"
include "dgraacl.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem dgraaf
  let cA: class A
  let vd: setvar d
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P


  assert |- degAA : AA --> NN

  proof
    caa
    cn
    cdgraa
    wf
    cdgraa
    caa
    wfn
    va
    cv
    #
    cdgraa
    cfv
    cn
    wcel
    #
    va
    caa
    wral
    va
    caa
    vp
    cv
    #
    cdgr
    cfv
    vb
    cv
    wceq
    @0
    @2
    cfv
    cc0
    wceq
    wa
    vp
    cq
    cply
    cfv
    c0p
    csn
    cdif
    wrex
    vb
    cn
    crab
    #
    cr
    clt
    cinf
    cdgraa
    cr
    @3
    clt
    ltso
    infex
    va
    vp
    vb
    df-dgraa
    fnmpti
    @1
    va
    caa
    @0
    dgraacl
    rgen
    va
    caa
    cn
    cdgraa
    ffnfv
    mpbir2an
end
