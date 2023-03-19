include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "cram.mm"
include "co.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "wss.mm"
include "pnfxr.mm"
include "snssi.mm"
include "ax-mp.mm"
include "unssi.mm"
include "ramcl2.mm"
include "sseldi.mm"

theorem ramxrcl
  let cR: class R
  let cF: class F
  let cM: class M
  let cV: class V


  assert |- ( ( M e. NN0 /\ R e. V /\ F : R --> NN0 ) -> ( M Ramsey F ) e. RR* )

  proof
    cM
    cn0
    wcel
    cR
    cV
    wcel
    cR
    cn0
    cF
    wf
    w3a
    cn0
    cpnf
    csn
    #
    cun
    cxr
    cM
    cF
    cram
    co
    cn0
    @0
    cxr
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    cpnf
    cxr
    wcel
    @0
    cxr
    wss
    pnfxr
    cpnf
    cxr
    snssi
    ax-mp
    unssi
    cR
    cF
    cM
    cV
    ramcl2
    sseldi
end
