include "cn0.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "wo.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "elun.mm"
include "nn0z.mm"
include "zltlem1.mm"
include "sylan.mm"
include "cr.mm"
include "zre.mm"
include "mnflt.mm"
include "syl.mm"
include "cxr.mm"
include "peano2zm.mm"
include "zred.mm"
include "rexrd.mm"
include "mnfle.mm"
include "2thd.mm"
include "wceq.mm"
include "elsni.mm"
include "breq1.mm"
include "bibi12d.mm"
include "syl5ibrcom.mm"
include "impcom.mm"
include "jaoian.mm"
include "sylanb.mm"

theorem degltlem1
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. ( NN0 u. { -oo } ) /\ Y e. ZZ ) -> ( X < Y <-> X <_ ( Y - 1 ) ) )

  proof
    cX
    cn0
    cmnf
    csn
    #
    cun
    wcel
    cX
    cn0
    wcel
    #
    cX
    @0
    wcel
    #
    wo
    cY
    cz
    wcel
    #
    cX
    cY
    clt
    wbr
    #
    cX
    cY
    c1
    cmin
    co
    #
    cle
    wbr
    #
    wb
    #
    cX
    cn0
    @0
    elun
    @1
    @3
    @7
    @2
    @1
    cX
    cz
    wcel
    @3
    @7
    cX
    nn0z
    cX
    cY
    zltlem1
    sylan
    @3
    @2
    @7
    @3
    @7
    @2
    cmnf
    cY
    clt
    wbr
    #
    cmnf
    @5
    cle
    wbr
    #
    wb
    #
    @3
    @8
    @9
    @3
    cY
    cr
    wcel
    @8
    cY
    zre
    cY
    mnflt
    syl
    @3
    @5
    cxr
    wcel
    @9
    @3
    @5
    @3
    @5
    cY
    peano2zm
    zred
    rexrd
    @5
    mnfle
    syl
    2thd
    @2
    cX
    cmnf
    wceq
    #
    @7
    @10
    wb
    cX
    cmnf
    elsni
    @11
    @4
    @8
    @6
    @9
    cX
    cmnf
    cY
    clt
    breq1
    cX
    cmnf
    @5
    cle
    breq1
    bibi12d
    syl
    syl5ibrcom
    impcom
    jaoian
    sylanb
end
