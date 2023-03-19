include "cnlm.mm"
include "wcel.mm"
include "ctmd.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "ctrg.mm"
include "w3a.mm"
include "cscaf.mm"
include "ctopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "ctlm.mm"
include "ctgp.mm"
include "cngp.mm"
include "cabl.mm"
include "nlmngp.mm"
include "nlmlmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "ngptgp.mm"
include "syl2anc.mm"
include "tgptmd.mm"
include "cnrg.mm"
include "eqid.mm"
include "nlmnrg.mm"
include "nrgtrg.mm"
include "3jca.mm"
include "nlmvscn.mm"
include "istlm.mm"
include "sylanbrc.mm"

theorem nlmtlm
  let cW: class W


  assert |- ( W e. NrmMod -> W e. TopMod )

  proof
    cW
    cnlm
    wcel
    #
    cW
    ctmd
    wcel
    #
    cW
    clmod
    wcel
    #
    cW
    csca
    cfv
    #
    ctrg
    wcel
    #
    w3a
    cW
    cscaf
    cfv
    #
    @3
    ctopn
    cfv
    #
    cW
    ctopn
    cfv
    #
    ctx
    co
    @7
    ccn
    co
    wcel
    cW
    ctlm
    wcel
    @0
    @1
    @2
    @4
    @0
    cW
    ctgp
    wcel
    #
    @1
    @0
    cW
    cngp
    wcel
    cW
    cabl
    wcel
    #
    @8
    cW
    nlmngp
    @0
    @2
    @9
    cW
    nlmlmod
    #
    cW
    lmodabl
    syl
    cW
    ngptgp
    syl2anc
    cW
    tgptmd
    syl
    @10
    @0
    @3
    cnrg
    wcel
    @4
    @3
    cW
    @3
    eqid
    #
    nlmnrg
    @3
    nrgtrg
    syl
    3jca
    @5
    @3
    @7
    @6
    cW
    @11
    @5
    eqid
    #
    @7
    eqid
    #
    @6
    eqid
    #
    nlmvscn
    @5
    @3
    @7
    @6
    cW
    @12
    @13
    @11
    @14
    istlm
    sylanbrc
end
