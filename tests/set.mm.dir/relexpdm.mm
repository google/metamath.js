include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "crelexp.mm"
include "co.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cuni.mm"
include "relexpdmg.mm"
include "dmrnssfld.mm"
include "syl6ss.mm"

theorem relexpdm
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. NN0 /\ R e. V ) -> dom ( R ^r N ) C_ U. U. R )

  proof
    cN
    cn0
    wcel
    cR
    cV
    wcel
    wa
    cR
    cN
    crelexp
    co
    cdm
    cR
    cdm
    cR
    crn
    cun
    cR
    cuni
    cuni
    cR
    cN
    cV
    relexpdmg
    cR
    dmrnssfld
    syl6ss
end
