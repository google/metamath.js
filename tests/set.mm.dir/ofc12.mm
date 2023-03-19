include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "cmpt.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "offval2.mm"
include "syl6eqr.mm"

theorem ofc12
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume ofc12.1: |- ( ph -> A e. V )
  assume ofc12.2: |- ( ph -> B e. W )
  assume ofc12.3: |- ( ph -> C e. X )


  assert |- ( ph -> ( ( A X. { B } ) oF R ( A X. { C } ) ) = ( A X. { ( B R C ) } ) )

  proof
    wph
    cA
    cB
    csn
    cxp
    #
    cA
    cC
    csn
    cxp
    #
    cR
    cof
    co
    vx
    cA
    cB
    cC
    cR
    co
    #
    cmpt
    cA
    @2
    csn
    cxp
    wph
    vx
    cA
    cB
    cC
    cR
    @0
    @1
    cV
    cW
    cX
    ofc12.1
    wph
    cB
    cW
    wcel
    vx
    cv
    cA
    wcel
    #
    ofc12.2
    adantr
    wph
    cC
    cX
    wcel
    @3
    ofc12.3
    adantr
    @0
    vx
    cA
    cB
    cmpt
    wceq
    wph
    vx
    cA
    cB
    fconstmpt
    a1i
    @1
    vx
    cA
    cC
    cmpt
    wceq
    wph
    vx
    cA
    cC
    fconstmpt
    a1i
    offval2
    vx
    cA
    @2
    fconstmpt
    syl6eqr
end
