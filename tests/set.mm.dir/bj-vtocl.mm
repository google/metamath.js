include "nfv.mm"
include "bj-vtoclf.mm"

theorem bj-vtocl
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-vtocl.s: |- A e. V
  assume bj-vtocl.maj: |- ( x = A -> ( ph <-> ps ) )
  assume bj-vtocl.min: |- ph

  disjoint A x
  disjoint ps x
  disjoint V x
  assert |- ps

  proof
    wph
    wps
    vx
    cA
    cV
    wps
    vx
    nfv
    bj-vtocl.s
    bj-vtocl.maj
    bj-vtocl.min
    bj-vtoclf
end
