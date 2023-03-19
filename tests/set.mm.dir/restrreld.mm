include "cvv.mm"
include "cres.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "syl6eq.mm"
include "xpintrreld.mm"

theorem restrreld
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  assume restrreld.r: |- ( ph -> ( R o. R ) C_ R )
  assume restrreld.s: |- ( ph -> S = ( R |` A ) )


  assert |- ( ph -> ( S o. S ) C_ S )

  proof
    wph
    cA
    cvv
    cR
    cS
    restrreld.r
    wph
    cS
    cR
    cA
    cres
    cR
    cA
    cvv
    cxp
    cin
    restrreld.s
    cR
    cA
    df-res
    syl6eq
    xpintrreld
end
