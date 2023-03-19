include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "cfv.mm"
include "isclm.mm"
include "simp2bi.mm"

theorem clmsca
  let cF: class F
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vk: setvar k
  let vw: setvar w
  assume isclm.f: |- F = ( Scalar ` W )
  assume isclm.k: |- K = ( Base ` F )


  assert |- ( W e. CMod -> F = ( CCfld |`s K ) )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cF
    ccnfld
    cK
    cress
    co
    wceq
    cK
    ccnfld
    csubrg
    cfv
    wcel
    cF
    cK
    cW
    isclm.f
    isclm.k
    isclm
    simp2bi
end
