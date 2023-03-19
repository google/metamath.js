include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "1fv.mm"
include "ancoms.mm"
include "simpld.mm"
include "cvv.mm"
include "wb.mm"
include "1vgrex.mm"
include "adantl.mm"
include "0wlk.mm"
include "syl.mm"
include "mpbird.mm"

theorem is0wlk
  let cP: class P
  let cG: class G
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( ( P = { <. 0 , N >. } /\ N e. V ) -> (/) ( Walks ` G ) P )

  proof
    cP
    cc0
    cN
    cop
    csn
    wceq
    #
    cN
    cV
    wcel
    #
    wa
    #
    c0
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cc0
    cfz
    co
    cV
    cP
    wf
    #
    @2
    @4
    cc0
    cP
    cfv
    cN
    wceq
    #
    @1
    @0
    @4
    @5
    wa
    cP
    cN
    cV
    1fv
    ancoms
    simpld
    @2
    cG
    cvv
    wcel
    #
    @3
    @4
    wb
    @1
    @6
    @0
    cG
    cN
    cV
    0wlk.v
    1vgrex
    adantl
    cP
    cvv
    cG
    cV
    0wlk.v
    0wlk
    syl
    mpbird
end
