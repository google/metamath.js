include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "bnj918.mm"

theorem bnj528
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vm: setvar m
  let cG: class G
  let vp: setvar p
  assume bnj528.1: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )


  assert |- G e. _V

  proof
    vy
    vp
    cv
    vf
    cv
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    vf
    vm
    cG
    bnj528.1
    bnj918
end
