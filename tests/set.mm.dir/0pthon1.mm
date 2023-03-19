include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cop.mm"
include "csn.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cpthson.mm"
include "wbr.mm"
include "eqidd.mm"
include "1fv.mm"
include "mpdan.mm"
include "0pthon.mm"
include "syl.mm"

theorem 0pthon1
  let cG: class G
  let cN: class N
  let cV: class V
  assume 0pthon.v: |- V = ( Vtx ` G )


  assert |- ( N e. V -> (/) ( N ( PathsOn ` G ) N ) { <. 0 , N >. } )

  proof
    cN
    cV
    wcel
    #
    cc0
    cc0
    cfz
    co
    cV
    cc0
    cN
    cop
    csn
    #
    wf
    cc0
    @1
    cfv
    cN
    wceq
    wa
    #
    c0
    @1
    cN
    cN
    cG
    cpthson
    cfv
    co
    wbr
    @0
    @1
    @1
    wceq
    @2
    @0
    @1
    eqidd
    @1
    cN
    cV
    1fv
    mpdan
    @1
    cG
    cN
    cV
    0pthon.v
    0pthon
    syl
end
