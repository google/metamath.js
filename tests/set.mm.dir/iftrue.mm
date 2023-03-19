include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "cab.mm"
include "cif.mm"
include "dedlem0a.mm"
include "abbi2dv.mm"
include "dfif2.mm"
include "syl6reqr.mm"

theorem iftrue
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C


  assert |- ( ph -> if ( ph , A , B ) = A )

  proof
    wph
    cA
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wi
    @0
    cA
    wcel
    #
    wph
    wa
    wi
    #
    vx
    cab
    wph
    cA
    cB
    cif
    wph
    @3
    vx
    cA
    wph
    @2
    @1
    dedlem0a
    abbi2dv
    wph
    vx
    cA
    cB
    dfif2
    syl6reqr
end
