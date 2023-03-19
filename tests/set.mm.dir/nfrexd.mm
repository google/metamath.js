include "wrex.mm"
include "wn.mm"
include "wral.mm"
include "dfrex2.mm"
include "nfnd.mm"
include "nfrald.mm"
include "nfxfrd.mm"

theorem nfrexd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfrexd.1: |- F/ y ph
  assume nfrexd.2: |- ( ph -> F/_ x A )
  assume nfrexd.3: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x E. y e. A ps )

  proof
    wps
    vy
    cA
    wrex
    wps
    wn
    #
    vy
    cA
    wral
    #
    wn
    wph
    vx
    wps
    vy
    cA
    dfrex2
    wph
    @1
    vx
    wph
    @0
    vx
    vy
    cA
    nfrexd.1
    nfrexd.2
    wph
    wps
    vx
    nfrexd.3
    nfnd
    nfrald
    nfnd
    nfxfrd
end
