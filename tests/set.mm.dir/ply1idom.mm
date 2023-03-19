include "ccrg.mm"
include "wcel.mm"
include "cdomn.mm"
include "wa.mm"
include "cidom.mm"
include "ply1crng.mm"
include "ply1domn.mm"
include "anim12i.mm"
include "isidom.mm"
include "3imtr4i.mm"

theorem ply1idom
  let cP: class P
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume ply1domn.p: |- P = ( Poly1 ` R )


  assert |- ( R e. IDomn -> P e. IDomn )

  proof
    cR
    ccrg
    wcel
    #
    cR
    cdomn
    wcel
    #
    wa
    cP
    ccrg
    wcel
    #
    cP
    cdomn
    wcel
    #
    wa
    cR
    cidom
    wcel
    cP
    cidom
    wcel
    @0
    @2
    @1
    @3
    cP
    cR
    ply1domn.p
    ply1crng
    cP
    cR
    ply1domn.p
    ply1domn
    anim12i
    cR
    isidom
    cP
    isidom
    3imtr4i
end
