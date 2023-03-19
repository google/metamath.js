include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "nfn.mm"
include "weq.mm"
include "notbid.mm"
include "cbvralcsf.mm"
include "notbii.mm"
include "dfrex2.mm"
include "3bitr4i.mm"

theorem cbvrexcsf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vz: setvar z
  assume cbvralcsf.1: |- F/_ y A
  assume cbvralcsf.2: |- F/_ x B
  assume cbvralcsf.3: |- F/ y ph
  assume cbvralcsf.4: |- F/ x ps
  assume cbvralcsf.5: |- ( x = y -> A = B )
  assume cbvralcsf.6: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( E. x e. A ph <-> E. y e. B ps )

  proof
    wph
    wn
    #
    vx
    cA
    wral
    #
    wn
    wps
    wn
    #
    vy
    cB
    wral
    #
    wn
    wph
    vx
    cA
    wrex
    wps
    vy
    cB
    wrex
    @1
    @3
    @0
    @2
    vx
    vy
    cA
    cB
    cbvralcsf.1
    cbvralcsf.2
    wph
    vy
    cbvralcsf.3
    nfn
    wps
    vx
    cbvralcsf.4
    nfn
    cbvralcsf.5
    vx
    vy
    weq
    wph
    wps
    cbvralcsf.6
    notbid
    cbvralcsf
    notbii
    wph
    vx
    cA
    dfrex2
    wps
    vy
    cB
    dfrex2
    3bitr4i
end
