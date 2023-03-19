include "bnj918.mm"
include "bnj1000.mm"

theorem bnj965
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cN: class N
  let bnjwpsn: wff ps"
  assume bnj965.1: |- ( ps <-> A. i e. _om ( suc i e. N -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj965.2: |- ( ps" <-> [. G / f ]. ps )
  assume bnj965.12000: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj965.13000: |- G = ( f u. { <. n , C >. } )

  disjoint A f
  disjoint G i
  disjoint N f
  disjoint R f
  disjoint f i
  disjoint f y
  disjoint i y
  disjoint n y
  assert |- ( ps" <-> A. i e. _om ( suc i e. N -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) ) )

  proof
    wps
    vy
    cA
    cC
    cR
    vf
    vi
    vm
    vn
    cG
    cN
    bnjwpsn
    bnj965.1
    bnj965.2
    cC
    vf
    vn
    cG
    bnj965.13000
    bnj918
    bnj965.12000
    bnj965.13000
    bnj1000
end
