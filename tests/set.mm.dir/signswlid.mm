include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "signspval.mm"
include "adantr.mm"
include "simpr.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem signswlid
  let c.pd: class .+^
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsw.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }

  disjoint a b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( ( ( X e. { -u 1 , 0 , 1 } /\ Y e. { -u 1 , 0 , 1 } ) /\ Y =/= 0 ) -> ( X .+^ Y ) = Y )

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
    wa
    #
    cY
    cc0
    wne
    #
    wa
    #
    cX
    cY
    c.pd
    co
    #
    cY
    cc0
    wceq
    #
    cX
    cY
    cif
    #
    cY
    @1
    @4
    @6
    wceq
    @2
    c.pd
    cX
    cY
    va
    vb
    signsw.p
    signspval
    adantr
    @3
    @5
    cX
    cY
    @3
    cY
    cc0
    @1
    @2
    simpr
    neneqd
    iffalsed
    eqtrd
end
