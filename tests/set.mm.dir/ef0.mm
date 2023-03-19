include "caddc.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cseq.mm"
include "ce.mm"
include "cli.mm"
include "wbr.mm"
include "c1.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "0cn.mm"
include "eqid.mm"
include "efcvg.mm"
include "ax-mp.mm"
include "ef0lem.mm"
include "climuni.mm"
include "mp2an.mm"

theorem ef0
  let vn: setvar n


  assert |- ( exp ` 0 ) = 1

  proof
    caddc
    vn
    cn0
    cc0
    vn
    cv
    #
    cexp
    co
    @0
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    cc0
    cseq
    #
    cc0
    ce
    cfv
    #
    cli
    wbr
    #
    @2
    c1
    cli
    wbr
    #
    @3
    c1
    wceq
    cc0
    cc
    wcel
    @4
    0cn
    cc0
    vn
    @1
    @1
    eqid
    #
    efcvg
    ax-mp
    cc0
    cc0
    wceq
    @5
    cc0
    eqid
    cc0
    vn
    @1
    @6
    ef0lem
    ax-mp
    @3
    c1
    @2
    climuni
    mp2an
end
