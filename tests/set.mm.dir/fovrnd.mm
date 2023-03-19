include "cxp.mm"
include "wf.mm"
include "wcel.mm"
include "co.mm"
include "fovrn.mm"
include "syl3anc.mm"

theorem fovrnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume fovrnd.1: |- ( ph -> F : ( R X. S ) --> C )
  assume fovrnd.2: |- ( ph -> A e. R )
  assume fovrnd.3: |- ( ph -> B e. S )


  assert |- ( ph -> ( A F B ) e. C )

  proof
    wph
    cR
    cS
    cxp
    cC
    cF
    wf
    cA
    cR
    wcel
    cB
    cS
    wcel
    cA
    cB
    cF
    co
    cC
    wcel
    fovrnd.1
    fovrnd.2
    fovrnd.3
    cA
    cB
    cC
    cR
    cS
    cF
    fovrn
    syl3anc
end
