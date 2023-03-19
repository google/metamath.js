include "cnvc.mm"
include "wcel.mm"
include "ctlm.mm"
include "csca.mm"
include "cfv.mm"
include "ctdrg.mm"
include "ctvc.mm"
include "cnlm.mm"
include "nvcnlm.mm"
include "nlmtlm.mm"
include "syl.mm"
include "cnrg.mm"
include "cdr.mm"
include "eqid.mm"
include "nlmnrg.mm"
include "clvec.mm"
include "nvclvec.mm"
include "lvecdrng.mm"
include "nrgtdrg.mm"
include "syl2anc.mm"
include "istvc.mm"
include "sylanbrc.mm"

theorem nvctvc
  let cW: class W


  assert |- ( W e. NrmVec -> W e. TopVec )

  proof
    cW
    cnvc
    wcel
    #
    cW
    ctlm
    wcel
    #
    cW
    csca
    cfv
    #
    ctdrg
    wcel
    #
    cW
    ctvc
    wcel
    @0
    cW
    cnlm
    wcel
    #
    @1
    cW
    nvcnlm
    #
    cW
    nlmtlm
    syl
    @0
    @2
    cnrg
    wcel
    #
    @2
    cdr
    wcel
    #
    @3
    @0
    @4
    @6
    @5
    @2
    cW
    @2
    eqid
    #
    nlmnrg
    syl
    @0
    cW
    clvec
    wcel
    @7
    cW
    nvclvec
    @2
    cW
    @8
    lvecdrng
    syl
    @2
    nrgtdrg
    syl2anc
    @2
    cW
    @8
    istvc
    sylanbrc
end
