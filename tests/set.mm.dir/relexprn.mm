include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "crelexp.mm"
include "co.mm"
include "crn.mm"
include "cdm.mm"
include "cun.mm"
include "cuni.mm"
include "relexprng.mm"
include "dmrnssfld.mm"
include "syl6ss.mm"

theorem relexprn
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. NN0 /\ R e. V ) -> ran ( R ^r N ) C_ U. U. R )

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
    crn
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
    relexprng
    cR
    dmrnssfld
    syl6ss
end
