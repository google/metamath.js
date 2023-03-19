include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "nfn.mm"
include "weq.mm"
include "notbid.mm"
include "cbvralf.mm"
include "notbii.mm"
include "dfrex2.mm"
include "3bitr4i.mm"

theorem cbvrexf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cbvralf.1: |- F/_ x A
  assume cbvralf.2: |- F/_ y A
  assume cbvralf.3: |- F/ y ph
  assume cbvralf.4: |- F/ x ps
  assume cbvralf.5: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( E. x e. A ph <-> E. y e. A ps )

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
    cA
    wral
    #
    wn
    wph
    vx
    cA
    wrex
    wps
    vy
    cA
    wrex
    @1
    @3
    @0
    @2
    vx
    vy
    cA
    cbvralf.1
    cbvralf.2
    wph
    vy
    cbvralf.3
    nfn
    wps
    vx
    cbvralf.4
    nfn
    vx
    vy
    weq
    wph
    wps
    cbvralf.5
    notbid
    cbvralf
    notbii
    wph
    vx
    cA
    dfrex2
    wps
    vy
    cA
    dfrex2
    3bitr4i
end
