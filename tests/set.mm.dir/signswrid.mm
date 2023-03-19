include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "c0ex.mm"
include "tpid2.mm"
include "signspval.mm"
include "mpan2.mm"
include "eqid.mm"
include "iftrue.mm"
include "mp1i.mm"
include "eqtrd.mm"

theorem signswrid
  let c.pd: class .+^
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsw.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }

  disjoint a b
  disjoint X a
  disjoint X b
  assert |- ( X e. { -u 1 , 0 , 1 } -> ( X .+^ 0 ) = X )

  proof
    cX
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    wcel
    #
    cX
    cc0
    c.pd
    co
    #
    cc0
    cc0
    wceq
    #
    cX
    cc0
    cif
    #
    cX
    @2
    cc0
    @1
    wcel
    @3
    @5
    wceq
    @0
    cc0
    c1
    c0ex
    tpid2
    c.pd
    cX
    cc0
    va
    vb
    signsw.p
    signspval
    mpan2
    @4
    @5
    cX
    wceq
    @2
    cc0
    eqid
    @4
    cX
    cc0
    iftrue
    mp1i
    eqtrd
end
