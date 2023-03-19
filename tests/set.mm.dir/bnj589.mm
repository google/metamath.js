include "cv.mm"
include "bnj222.mm"

theorem bnj589
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vn: setvar n
  assume bnj589.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  disjoint A i
  disjoint A k
  disjoint i k
  disjoint R i
  disjoint R k
  disjoint f i
  disjoint f k
  disjoint f y
  disjoint i y
  disjoint k y
  disjoint i n
  disjoint k n
  assert |- ( ps <-> A. k e. _om ( suc k e. n -> ( f ` suc k ) = U_ y e. ( f ` k ) _pred ( y , A , R ) ) )

  proof
    wps
    vy
    cA
    cR
    vi
    vk
    vf
    cv
    vn
    cv
    bnj589.1
    bnj222
end
