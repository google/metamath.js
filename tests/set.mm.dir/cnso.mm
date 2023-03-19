include "cr.mm"
include "cc.mm"
include "cv.mm"
include "wf1o.mm"
include "wor.mm"
include "wex.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "copab.mm"
include "cxp.mm"
include "cin.mm"
include "ltso.mm"
include "wiso.mm"
include "wb.mm"
include "eqid.mm"
include "f1oiso.mm"
include "mpan2.mm"
include "isoso.mm"
include "soinxp.mm"
include "syl6bb.mm"
include "syl.mm"
include "mpbii.mm"
include "cnex.mm"
include "xpex.mm"
include "inex2.mm"
include "soeq1.mm"
include "spcev.mm"
include "cen.mm"
include "cn.mm"
include "cpw.mm"
include "rpnnen.mm"
include "cpnnen.mm"
include "entr4i.mm"
include "bren.mm"
include "mpbi.mm"
include "exlimiiv.mm"

theorem cnso
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e


  assert |- E. x x Or CC

  proof
    cr
    cc
    va
    cv
    #
    wf1o
    #
    cc
    vx
    cv
    #
    wor
    #
    vx
    wex
    #
    va
    @1
    cc
    vb
    cv
    vd
    cv
    #
    @0
    cfv
    wceq
    vc
    cv
    ve
    cv
    #
    @0
    cfv
    wceq
    wa
    @5
    @6
    clt
    wbr
    wa
    ve
    cr
    wrex
    vd
    cr
    wrex
    vb
    vc
    copab
    #
    cc
    cc
    cxp
    #
    cin
    #
    wor
    #
    @4
    @1
    cr
    clt
    wor
    #
    @10
    ltso
    @1
    cr
    cc
    clt
    @7
    @0
    wiso
    #
    @11
    @10
    wb
    @1
    @7
    @7
    wceq
    @12
    @7
    eqid
    vd
    ve
    vb
    vc
    cr
    cc
    clt
    @7
    @0
    f1oiso
    mpan2
    @12
    @11
    cc
    @7
    wor
    @10
    cr
    cc
    clt
    @7
    @0
    isoso
    cc
    @7
    soinxp
    syl6bb
    syl
    mpbii
    @3
    @10
    vx
    @9
    @8
    @7
    cc
    cc
    cnex
    cnex
    xpex
    inex2
    cc
    @2
    @9
    soeq1
    spcev
    syl
    cr
    cc
    cen
    wbr
    @1
    va
    wex
    cr
    cn
    cpw
    cc
    rpnnen
    cpnnen
    entr4i
    cr
    cc
    va
    bren
    mpbi
    exlimiiv
end
