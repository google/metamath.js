include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt2.mm"
include "cme.mm"
include "cmopn.mm"
include "wceq.mm"
include "wrex.mm"
include "crp.mm"
include "1rp.mm"
include "eqid.mm"
include "stdbdmet.mm"
include "mpan2.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "0lt1.mm"
include "stdbdmopn.mm"
include "mp3an23.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem mopnex
  let cD: class D
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  assume mopnex.1: |- J = ( MetOpen ` D )

  disjoint D d
  disjoint J d
  disjoint X d
  disjoint d x
  disjoint d y
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint X x
  disjoint X y
  assert |- ( D e. ( *Met ` X ) -> E. d e. ( Met ` X ) J = ( MetOpen ` d ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    vx
    vy
    cX
    cX
    vx
    cv
    vy
    cv
    cD
    co
    #
    c1
    cle
    wbr
    @1
    c1
    cif
    cmpt2
    #
    cX
    cme
    cfv
    #
    wcel
    #
    cJ
    @2
    cmopn
    cfv
    #
    wceq
    #
    cJ
    vd
    cv
    #
    cmopn
    cfv
    #
    wceq
    #
    vd
    @3
    wrex
    @0
    c1
    crp
    wcel
    #
    @4
    1rp
    vx
    vy
    cD
    @2
    c1
    cX
    @2
    eqid
    #
    stdbdmet
    mpan2
    @0
    c1
    cxr
    wcel
    #
    cc0
    c1
    clt
    wbr
    @6
    @10
    @12
    1rp
    c1
    rpxr
    ax-mp
    0lt1
    vx
    vy
    cD
    @2
    c1
    cJ
    cX
    @11
    mopnex.1
    stdbdmopn
    mp3an23
    @9
    @6
    vd
    @2
    @3
    @7
    @2
    wceq
    @8
    @5
    cJ
    @7
    @2
    cmopn
    fveq2
    eqeq2d
    rspcev
    syl2anc
end
