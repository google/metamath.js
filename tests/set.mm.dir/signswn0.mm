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
include "neeq1.mm"
include "simplr.mm"
include "wn.mm"
include "simpr.mm"
include "neqned.mm"
include "ifbothda.mm"
include "eqnetrd.mm"

theorem signswn0
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
  assert |- ( ( ( X e. { -u 1 , 0 , 1 } /\ Y e. { -u 1 , 0 , 1 } ) /\ X =/= 0 ) -> ( X .+^ Y ) =/= 0 )

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
    cX
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
    cc0
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
    @5
    @2
    cY
    cc0
    wne
    @6
    cc0
    wne
    @3
    cX
    cY
    cX
    @6
    cc0
    neeq1
    cY
    @6
    cc0
    neeq1
    @1
    @2
    @5
    simplr
    @3
    @5
    wn
    #
    wa
    cY
    cc0
    @3
    @7
    simpr
    neqned
    ifbothda
    eqnetrd
end
