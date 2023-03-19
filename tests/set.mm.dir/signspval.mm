include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "wcel.mm"
include "wceq.mm"
include "cif.mm"
include "co.mm"
include "ifcl.mm"
include "cv.mm"
include "ifeq1.mm"
include "eqeq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"

theorem signspval
  let c.pd: class .+^
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )

  disjoint a b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( ( X e. { -u 1 , 0 , 1 } /\ Y e. { -u 1 , 0 , 1 } ) -> ( X .+^ Y ) = if ( Y = 0 , X , Y ) )

  proof
    cX
    c1
    cneg
    cc0
    c1
    ctp
    #
    wcel
    cY
    @0
    wcel
    cY
    cc0
    wceq
    #
    cX
    cY
    cif
    #
    @0
    wcel
    cX
    cY
    c.pd
    co
    @2
    wceq
    @1
    cX
    cY
    @0
    ifcl
    va
    vb
    cX
    cY
    @0
    @0
    vb
    cv
    #
    cc0
    wceq
    #
    va
    cv
    #
    @3
    cif
    @2
    c.pd
    @4
    cX
    @3
    cif
    @0
    @4
    @5
    cX
    @3
    ifeq1
    @3
    cY
    wceq
    #
    @4
    @1
    @3
    cY
    cX
    @3
    cY
    cc0
    eqeq1
    @6
    id
    ifbieq2d
    signsw.p
    ovmpt2g
    mpd3an3
end
