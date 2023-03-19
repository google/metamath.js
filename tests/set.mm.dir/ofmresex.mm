include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "cof.mm"
include "cres.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ofexg.mm"
include "syl.mm"

theorem ofmresex
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume ofmresex.a: |- ( ph -> A e. V )
  assume ofmresex.b: |- ( ph -> B e. W )


  assert |- ( ph -> ( oF R |` ( A X. B ) ) e. _V )

  proof
    wph
    cA
    cB
    cxp
    #
    cvv
    wcel
    #
    cR
    cof
    @0
    cres
    cvv
    wcel
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @1
    ofmresex.a
    ofmresex.b
    cA
    cB
    cV
    cW
    xpexg
    syl2anc
    @0
    cR
    cvv
    ofexg
    syl
end
