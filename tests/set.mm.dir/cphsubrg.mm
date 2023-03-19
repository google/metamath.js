include "ccph.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "cin.mm"
include "csubrg.mm"
include "cfv.mm"
include "cphsca.mm"
include "clvec.mm"
include "cdr.mm"
include "cphlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "cphsubrglem.mm"
include "simp3d.mm"

theorem cphsubrg
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( W e. CPreHil -> K e. ( SubRing ` CCfld ) )

  proof
    cW
    ccph
    wcel
    #
    cF
    ccnfld
    cK
    cress
    co
    wceq
    cK
    cK
    cc
    cin
    wceq
    cK
    ccnfld
    csubrg
    cfv
    wcel
    @0
    cK
    cF
    cK
    cphsca.k
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsca
    @0
    cW
    clvec
    wcel
    cF
    cdr
    wcel
    cW
    cphlvec
    cF
    cW
    cphsca.f
    lvecdrng
    syl
    cphsubrglem
    simp3d
end
