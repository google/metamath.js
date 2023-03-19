include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wfn.mm"
include "measfrge0.mm"
include "ffn.mm"
include "syl.mm"

theorem measfn
  let cS: class S
  let cM: class M


  assert |- ( M e. ( measures ` S ) -> M Fn S )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    cS
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    cM
    cS
    wfn
    cS
    cM
    measfrge0
    cS
    @0
    cM
    ffn
    syl
end
