include "wi.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "con34b.mm"
include "ralbii.mm"
include "r19.21v.mm"
include "dfrex2.mm"
include "imbi1i.mm"
include "con1b.mm"
include "bitr2i.mm"
include "3bitri.mm"

theorem r19.23v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ps x
  assert |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    cA
    wral
    wps
    wn
    #
    wph
    wn
    #
    wi
    #
    vx
    cA
    wral
    @1
    @2
    vx
    cA
    wral
    #
    wi
    #
    wph
    vx
    cA
    wrex
    #
    wps
    wi
    #
    @0
    @3
    vx
    cA
    wph
    wps
    con34b
    ralbii
    @1
    @2
    vx
    cA
    r19.21v
    @7
    @4
    wn
    #
    wps
    wi
    @5
    @6
    @8
    wps
    wph
    vx
    cA
    dfrex2
    imbi1i
    @4
    wps
    con1b
    bitr2i
    3bitri
end
