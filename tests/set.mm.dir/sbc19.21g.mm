include "wcel.mm"
include "wi.mm"
include "wsbc.mm"
include "sbcimg.mm"
include "sbcgf.mm"
include "imbi1d.mm"
include "bitrd.mm"

theorem sbc19.21g
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcgf.1: |- F/ x ph


  assert |- ( A e. V -> ( [. A / x ]. ( ph -> ps ) <-> ( ph -> [. A / x ]. ps ) ) )

  proof
    cA
    cV
    wcel
    #
    wph
    wps
    wi
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    #
    wi
    wph
    @2
    wi
    wph
    wps
    vx
    cA
    cV
    sbcimg
    @0
    @1
    wph
    @2
    wph
    vx
    cA
    cV
    sbcgf.1
    sbcgf
    imbi1d
    bitrd
end
