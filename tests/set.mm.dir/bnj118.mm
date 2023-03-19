include "c1o.mm"
include "wsbc.mm"
include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "bnj105.mm"
include "bnj91.mm"
include "bitri.mm"

theorem bnj118
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let bnjwphm: wff ph'
  assume bnj118.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj118.2: |- ( ph' <-> [. 1o / n ]. ph )

  disjoint A n
  disjoint R n
  disjoint f n
  disjoint n x
  assert |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )

  proof
    bnjwphm
    wph
    vn
    c1o
    wsbc
    c0
    vf
    cv
    cfv
    cA
    cR
    vx
    cv
    c-bnj14
    wceq
    bnj118.2
    wph
    vx
    vn
    cA
    cR
    vf
    c1o
    bnj118.1
    bnj105
    bnj91
    bitri
end
