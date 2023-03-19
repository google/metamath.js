include "csn.mm"
include "wrex.mm"
include "wsbc.mm"
include "wcel.mm"
include "rexsns.mm"
include "sbciegf.mm"
include "syl5bb.mm"

theorem rexsngf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume rexsngf.1: |- F/ x ps
  assume rexsngf.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A e. V -> ( E. x e. { A } ph <-> ps ) )

  proof
    wph
    vx
    cA
    csn
    wrex
    wph
    vx
    cA
    wsbc
    cA
    cV
    wcel
    wps
    wph
    vx
    cA
    rexsns
    wph
    wps
    vx
    cA
    cV
    rexsngf.1
    rexsngf.2
    sbciegf
    syl5bb
end
