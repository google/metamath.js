include "wcel.mm"
include "c0.mm"
include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cspths.mm"
include "0trl.mm"
include "anbi1d.mm"
include "isspth.mm"
include "csn.mm"
include "fz0sn.mm"
include "feq2i.mm"
include "cop.mm"
include "wceq.mm"
include "c0ex.mm"
include "fsn2.mm"
include "funcnvsn.mm"
include "cnveq.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "simplbiim.mm"
include "sylbi.mm"
include "pm4.71i.mm"
include "3bitr4g.mm"

theorem 0spth
  let cP: class P
  let cG: class G
  let cV: class V
  let cW: class W
  assume 0pth.v: |- V = ( Vtx ` G )


  assert |- ( G e. W -> ( (/) ( SPaths ` G ) P <-> P : ( 0 ... 0 ) --> V ) )

  proof
    cG
    cW
    wcel
    #
    c0
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    ccnv
    #
    wfun
    #
    wa
    cc0
    cc0
    cfz
    co
    #
    cV
    cP
    wf
    #
    @3
    wa
    c0
    cP
    cG
    cspths
    cfv
    wbr
    @5
    @0
    @1
    @5
    @3
    cP
    cW
    cG
    cV
    0pth.v
    0trl
    anbi1d
    cP
    c0
    cG
    isspth
    @5
    @3
    @5
    cc0
    csn
    #
    cV
    cP
    wf
    #
    @3
    @4
    @6
    cV
    cP
    fz0sn
    feq2i
    @7
    cc0
    cP
    cfv
    #
    cV
    wcel
    cP
    cc0
    @8
    cop
    csn
    #
    wceq
    #
    @3
    cc0
    cV
    cP
    c0ex
    fsn2
    @10
    @3
    @9
    ccnv
    #
    wfun
    cc0
    @8
    funcnvsn
    @10
    @2
    @11
    cP
    @9
    cnveq
    funeqd
    mpbiri
    simplbiim
    sylbi
    pm4.71i
    3bitr4g
end
