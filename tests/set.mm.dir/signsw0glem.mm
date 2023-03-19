include "cc0.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "ctp.mm"
include "wcel.mm"
include "cif.mm"
include "c0ex.mm"
include "tpid2.mm"
include "signspval.mm"
include "mpan.mm"
include "iftrue.mm"
include "id.mm"
include "eqtr4d.mm"
include "iffalse.mm"
include "pm2.61i.mm"
include "syl6eq.mm"
include "mpan2.mm"
include "eqid.mm"
include "iftruei.mm"
include "jca.mm"
include "rgen.mm"

theorem signsw0glem
  let vu: setvar u
  let c.pd: class .+^
  let va: setvar a
  let vb: setvar b
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )

  disjoint a b
  disjoint a u
  disjoint b u
  assert |- A. u e. { -u 1 , 0 , 1 } ( ( 0 .+^ u ) = u /\ ( u .+^ 0 ) = u )

  proof
    cc0
    vu
    cv
    #
    c.pd
    co
    #
    @0
    wceq
    #
    @0
    cc0
    c.pd
    co
    #
    @0
    wceq
    #
    wa
    vu
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    @0
    @6
    wcel
    #
    @2
    @4
    @7
    @1
    @0
    cc0
    wceq
    #
    cc0
    @0
    cif
    #
    @0
    cc0
    @6
    wcel
    #
    @7
    @1
    @9
    wceq
    @5
    cc0
    c1
    c0ex
    tpid2
    #
    c.pd
    cc0
    @0
    va
    vb
    signsw.p
    signspval
    mpan
    @8
    @9
    @0
    wceq
    @8
    @9
    cc0
    @0
    @8
    cc0
    @0
    iftrue
    @8
    id
    eqtr4d
    @8
    cc0
    @0
    iffalse
    pm2.61i
    syl6eq
    @7
    @3
    cc0
    cc0
    wceq
    #
    @0
    cc0
    cif
    #
    @0
    @7
    @10
    @3
    @13
    wceq
    @11
    c.pd
    @0
    cc0
    va
    vb
    signsw.p
    signspval
    mpan2
    @12
    @0
    cc0
    cc0
    eqid
    iftruei
    syl6eq
    jca
    rgen
end
