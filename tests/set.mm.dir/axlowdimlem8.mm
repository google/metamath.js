include "c3.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cop.mm"
include "csn.mm"
include "cfz.mm"
include "co.mm"
include "cdif.mm"
include "cc0.mm"
include "cxp.mm"
include "cun.mm"
include "fveq1i.mm"
include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "3re.mm"
include "elexi.mm"
include "negex.mm"
include "fnsn.mm"
include "wf.mm"
include "c0ex.mm"
include "fconst.mm"
include "ffn.mm"
include "ax-mp.mm"
include "disjdif.mm"
include "snid.mm"
include "pm3.2i.mm"
include "fvun1.mm"
include "mp3an.mm"
include "fvsn.mm"
include "3eqtri.mm"

theorem axlowdimlem8
  let cP: class P
  let cN: class N
  assume axlowdimlem7.1: |- P = ( { <. 3 , -u 1 >. } u. ( ( ( 1 ... N ) \ { 3 } ) X. { 0 } ) )


  assert |- ( P ` 3 ) = -u 1

  proof
    c3
    cP
    cfv
    c3
    c3
    c1
    cneg
    #
    cop
    csn
    #
    c1
    cN
    cfz
    co
    #
    c3
    csn
    #
    cdif
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    cfv
    #
    c3
    @1
    cfv
    #
    @0
    c3
    cP
    @7
    axlowdimlem7.1
    fveq1i
    @1
    @3
    wfn
    @6
    @4
    wfn
    #
    @3
    @4
    cin
    c0
    wceq
    #
    c3
    @3
    wcel
    #
    wa
    @8
    @9
    wceq
    c3
    @0
    c3
    cr
    3re
    elexi
    #
    c1
    negex
    #
    fnsn
    @4
    @5
    @6
    wf
    @10
    @4
    cc0
    c0ex
    fconst
    @4
    @5
    @6
    ffn
    ax-mp
    @11
    @12
    @3
    @2
    disjdif
    c3
    @13
    snid
    pm3.2i
    @3
    @4
    @1
    @6
    c3
    fvun1
    mp3an
    c3
    @0
    @13
    @14
    fvsn
    3eqtri
end
