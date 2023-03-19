include "clmod.mm"
include "wcel.mm"
include "clinds.mm"
include "cfv.mm"
include "wf1.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "ccom.mm"
include "clindf.mm"
include "wceq.mm"
include "wf.mm"
include "f1f.mm"
include "fcoi2.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "wbr.mm"
include "cdm.mm"
include "simp1.mm"
include "linds2.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "dmresi.mm"
include "f1eq3.mm"
include "ax-mp.mm"
include "biimpri.mm"
include "f1lindf.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"

theorem f1linds
  let cD: class D
  let cS: class S
  let cF: class F
  let cW: class W


  assert |- ( ( W e. LMod /\ S e. ( LIndS ` W ) /\ F : D -1-1-> S ) -> F LIndF W )

  proof
    cW
    clmod
    wcel
    #
    cS
    cW
    clinds
    cfv
    wcel
    #
    cD
    cS
    cF
    wf1
    #
    w3a
    #
    cid
    cS
    cres
    #
    cF
    ccom
    #
    cF
    cW
    clindf
    @2
    @0
    @5
    cF
    wceq
    #
    @1
    @2
    cD
    cS
    cF
    wf
    @6
    cD
    cS
    cF
    f1f
    cD
    cS
    cF
    fcoi2
    syl
    3ad2ant3
    @3
    @0
    @4
    cW
    clindf
    wbr
    #
    cD
    @4
    cdm
    #
    cF
    wf1
    #
    @5
    cW
    clindf
    wbr
    @0
    @1
    @2
    simp1
    @1
    @0
    @7
    @2
    cW
    cS
    linds2
    3ad2ant2
    @2
    @0
    @9
    @1
    @9
    @2
    @8
    cS
    wceq
    @9
    @2
    wb
    cS
    dmresi
    @8
    cS
    cD
    cF
    f1eq3
    ax-mp
    biimpri
    3ad2ant3
    @4
    cF
    cD
    cW
    f1lindf
    syl3anc
    eqbrtrrd
end
