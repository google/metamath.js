include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "c0.mm"
include "chash.mm"
include "wceq.mm"
include "cwlks.mm"
include "wbr.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cclwlks.mm"
include "0wlk.mm"
include "anbi2d.mm"
include "isclwlk.mm"
include "ancom.mm"
include "bitri.mm"
include "hash0.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "biantrur.mm"
include "3bitr4g.mm"

theorem 0clwlk
  let cP: class P
  let cG: class G
  let cV: class V
  let cX: class X
  assume 0clwlk.v: |- V = ( Vtx ` G )


  assert |- ( G e. X -> ( (/) ( ClWalks ` G ) P <-> P : ( 0 ... 0 ) --> V ) )

  proof
    cG
    cX
    wcel
    #
    cc0
    cP
    cfv
    c0
    chash
    cfv
    #
    cP
    cfv
    wceq
    #
    c0
    cP
    cG
    cwlks
    cfv
    wbr
    #
    wa
    #
    @2
    cc0
    cc0
    cfz
    co
    cV
    cP
    wf
    #
    wa
    c0
    cP
    cG
    cclwlks
    cfv
    wbr
    #
    @5
    @0
    @3
    @5
    @2
    cP
    cX
    cG
    cV
    0clwlk.v
    0wlk
    anbi2d
    @6
    @3
    @2
    wa
    @4
    cP
    c0
    cG
    isclwlk
    @3
    @2
    ancom
    bitri
    @2
    @5
    cc0
    @1
    cP
    @1
    cc0
    hash0
    eqcomi
    fveq2i
    biantrur
    3bitr4g
end
