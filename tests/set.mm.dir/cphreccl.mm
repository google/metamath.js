include "ccph.mm"
include "wcel.mm"
include "cphsca.mm"
include "clvec.mm"
include "cdr.mm"
include "cphlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "cphreccllem.mm"

theorem cphreccl
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ A e. K /\ A =/= 0 ) -> ( 1 / A ) e. K )

  proof
    cW
    ccph
    wcel
    #
    cK
    cF
    cK
    cA
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
    cphreccllem
end
