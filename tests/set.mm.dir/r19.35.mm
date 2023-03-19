include "wral.mm"
include "wn.mm"
include "wi.mm"
include "wrex.mm"
include "wa.mm"
include "r19.26.mm"
include "annim.mm"
include "ralbii.mm"
include "df-an.mm"
include "3bitr3i.mm"
include "con2bii.mm"
include "dfrex2.mm"
include "imbi2i.mm"
include "3bitr4ri.mm"

theorem r19.35
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A ( ph -> ps ) <-> ( A. x e. A ph -> E. x e. A ps ) )

  proof
    wph
    vx
    cA
    wral
    #
    wps
    wn
    #
    vx
    cA
    wral
    #
    wn
    #
    wi
    #
    wph
    wps
    wi
    #
    wn
    #
    vx
    cA
    wral
    #
    wn
    @0
    wps
    vx
    cA
    wrex
    #
    wi
    @5
    vx
    cA
    wrex
    @7
    @4
    wph
    @1
    wa
    #
    vx
    cA
    wral
    @0
    @2
    wa
    @7
    @4
    wn
    wph
    @1
    vx
    cA
    r19.26
    @9
    @6
    vx
    cA
    wph
    wps
    annim
    ralbii
    @0
    @2
    df-an
    3bitr3i
    con2bii
    @8
    @3
    @0
    wps
    vx
    cA
    dfrex2
    imbi2i
    @5
    vx
    cA
    dfrex2
    3bitr4ri
end
