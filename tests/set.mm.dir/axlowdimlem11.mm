include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cfz.mm"
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
include "ovex.mm"
include "1ex.mm"
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

theorem axlowdimlem11
  let cQ: class Q
  let cI: class I
  let cN: class N
  assume axlowdimlem10.1: |- Q = ( { <. ( I + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( I + 1 ) } ) X. { 0 } ) )


  assert |- ( Q ` ( I + 1 ) ) = 1

  proof
    cI
    c1
    caddc
    co
    #
    cQ
    cfv
    @0
    @0
    c1
    cop
    csn
    #
    c1
    cN
    cfz
    co
    #
    @0
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
    @0
    @1
    cfv
    #
    c1
    @0
    cQ
    @7
    axlowdimlem10.1
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
    @0
    @3
    wcel
    #
    wa
    @8
    @9
    wceq
    @0
    c1
    cI
    c1
    caddc
    ovex
    #
    1ex
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
    @0
    @13
    snid
    pm3.2i
    @3
    @4
    @1
    @6
    @0
    fvun1
    mp3an
    @0
    c1
    @13
    1ex
    fvsn
    3eqtri
end
