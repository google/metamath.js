include "c0g.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "ctp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "c0ex.mm"
include "tpid2.mm"
include "signsw0glem.mm"
include "pm3.2i.mm"
include "wb.mm"
include "wtru.mm"
include "signswbase.mm"
include "eqid.mm"
include "signswplusg.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "a1i.mm"
include "ismgmid.mm"
include "trud.mm"
include "mpbi.mm"
include "eqcomi.mm"

theorem signsw0g
  let c.pd: class .+^
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let ve: setvar e
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsw.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }

  disjoint a b
  disjoint a u
  disjoint b u
  disjoint e u
  disjoint .+^ e
  disjoint .+^ u
  disjoint W e
  disjoint W u
  assert |- 0 = ( 0g ` W )

  proof
    cW
    c0g
    cfv
    #
    cc0
    cc0
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    wcel
    #
    cc0
    vu
    cv
    #
    c.pd
    co
    #
    @4
    wceq
    #
    @4
    cc0
    c.pd
    co
    #
    @4
    wceq
    #
    wa
    #
    vu
    @2
    wral
    #
    wa
    #
    @0
    cc0
    wceq
    #
    @3
    @10
    @1
    cc0
    c1
    c0ex
    tpid2
    #
    vu
    c.pd
    va
    vb
    signsw.p
    signsw0glem
    #
    pm3.2i
    @11
    @12
    wb
    wtru
    vu
    @2
    c.pd
    cc0
    ve
    cW
    @0
    c.pd
    cW
    va
    vb
    signsw.p
    signsw.w
    signswbase
    @0
    eqid
    c.pd
    cW
    va
    vb
    signsw.p
    signsw.w
    signswplusg
    ve
    cv
    #
    @4
    c.pd
    co
    #
    @4
    wceq
    #
    @4
    @15
    c.pd
    co
    #
    @4
    wceq
    #
    wa
    #
    vu
    @2
    wral
    #
    ve
    @2
    wrex
    #
    wtru
    @3
    @10
    @22
    @13
    @14
    @21
    @10
    ve
    cc0
    @2
    @15
    cc0
    wceq
    #
    @20
    @9
    vu
    @2
    @23
    @17
    @6
    @19
    @8
    @23
    @16
    @5
    @4
    @15
    cc0
    @4
    c.pd
    oveq1
    eqeq1d
    @23
    @18
    @7
    @4
    @15
    cc0
    @4
    c.pd
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    mp2an
    a1i
    ismgmid
    trud
    mpbi
    eqcomi
end
