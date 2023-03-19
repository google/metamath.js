include "wsbc.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "sbcbii.mm"
include "bnj525.mm"
include "3bitri.mm"

theorem bnj523
  let wph: wff ph
  let cA: class A
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let bnjwphm: wff ph'
  assume bnj523.1: |- ( ph <-> ( F ` (/) ) = _pred ( X , A , R ) )
  assume bnj523.2: |- ( ph' <-> [. M / n ]. ph )
  assume bnj523.3: |- M e. _V

  disjoint A n
  disjoint F n
  disjoint R n
  disjoint X n
  assert |- ( ph' <-> ( F ` (/) ) = _pred ( X , A , R ) )

  proof
    bnjwphm
    wph
    vn
    cM
    wsbc
    c0
    cF
    cfv
    cA
    cR
    cX
    c-bnj14
    wceq
    #
    vn
    cM
    wsbc
    @0
    bnj523.2
    wph
    @0
    vn
    cM
    bnj523.1
    sbcbii
    @0
    vn
    cM
    bnj523.3
    bnj525
    3bitri
end
