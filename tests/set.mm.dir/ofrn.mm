include "cof.mm"
include "co.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "fovrnda.mm"
include "inidm.mm"
include "off.mm"
include "frn.mm"
include "syl.mm"

theorem ofrn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume ofrn.1: |- ( ph -> F : A --> B )
  assume ofrn.2: |- ( ph -> G : A --> B )
  assume ofrn.3: |- ( ph -> .+ : ( B X. B ) --> C )
  assume ofrn.4: |- ( ph -> A e. V )


  assert |- ( ph -> ran ( F oF .+ G ) C_ C )

  proof
    wph
    cA
    cC
    cF
    cG
    c.pl
    cof
    co
    #
    wf
    @0
    crn
    cC
    wss
    wph
    vx
    vy
    cA
    cA
    cA
    c.pl
    cB
    cB
    cC
    cF
    cG
    cV
    cV
    wph
    vx
    cv
    vy
    cv
    cC
    cB
    cB
    c.pl
    ofrn.3
    fovrnda
    ofrn.1
    ofrn.2
    ofrn.4
    ofrn.4
    cA
    inidm
    off
    cA
    cC
    @0
    frn
    syl
end
