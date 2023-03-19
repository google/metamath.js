include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ce.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "eff.mm"
include "ffn.mm"
include "ax-mp.mm"
include "wne.mm"
include "efcl.mm"
include "efne0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem eff2
  let vx: setvar x


  assert |- exp : CC --> ( CC \ { 0 } )

  proof
    cc
    cc
    cc0
    csn
    cdif
    #
    ce
    wf
    ce
    cc
    wfn
    #
    vx
    cv
    #
    ce
    cfv
    #
    @0
    wcel
    #
    vx
    cc
    wral
    cc
    cc
    ce
    wf
    @1
    eff
    cc
    cc
    ce
    ffn
    ax-mp
    @4
    vx
    cc
    @2
    cc
    wcel
    @3
    cc
    wcel
    @3
    cc0
    wne
    @4
    @2
    efcl
    @2
    efne0
    @3
    cc
    cc0
    eldifsn
    sylanbrc
    rgen
    vx
    cc
    @0
    ce
    ffnfv
    mpbir2an
end
