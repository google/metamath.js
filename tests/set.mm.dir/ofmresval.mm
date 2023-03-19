include "wcel.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "wceq.mm"
include "ovres.mm"
include "syl2anc.mm"

theorem ofmresval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  assume ofmresval.f: |- ( ph -> F e. A )
  assume ofmresval.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( F ( oF R |` ( A X. B ) ) G ) = ( F oF R G ) )

  proof
    wph
    cF
    cA
    wcel
    cG
    cB
    wcel
    cF
    cG
    cR
    cof
    #
    cA
    cB
    cxp
    cres
    co
    cF
    cG
    @0
    co
    wceq
    ofmresval.f
    ofmresval.g
    cF
    cG
    cA
    cB
    @0
    ovres
    syl2anc
end
