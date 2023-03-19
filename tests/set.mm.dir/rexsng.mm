include "csn.mm"
include "wrex.mm"
include "wsbc.mm"
include "wcel.mm"
include "rexsns.mm"
include "sbcieg.mm"
include "syl5bb.mm"

theorem rexsng
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume ralsng.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
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
    ralsng.1
    sbcieg
    syl5bb
end
