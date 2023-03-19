include "cid.mm"
include "cres.mm"
include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "dmresi.mm"
include "dmfi.mm"
include "syl5eqelr.mm"
include "wfn.mm"
include "wfun.mm"
include "funi.mm"
include "funfn.mm"
include "mpbi.mm"
include "resfnfinfin.mm"
include "mpan.mm"
include "impbii.mm"

theorem residfi
  let cA: class A


  assert |- ( ( _I |` A ) e. Fin <-> A e. Fin )

  proof
    cid
    cA
    cres
    #
    cfn
    wcel
    #
    cA
    cfn
    wcel
    #
    @1
    cA
    @0
    cdm
    cfn
    cA
    dmresi
    @0
    dmfi
    syl5eqelr
    cid
    cid
    cdm
    #
    wfn
    #
    @2
    @1
    cid
    wfun
    @4
    funi
    cid
    funfn
    mpbi
    @3
    cA
    cid
    resfnfinfin
    mpan
    impbii
end
