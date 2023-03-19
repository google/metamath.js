include "wcel.mm"
include "c0.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "ctrls.mm"
include "0wlk.mm"
include "anbi1d.mm"
include "istrl.mm"
include "funcnv0.mm"
include "biantru.mm"
include "3bitr4g.mm"

theorem 0trl
  let cP: class P
  let cU: class U
  let cG: class G
  let cV: class V
  let vk: setvar k
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( G e. U -> ( (/) ( Trails ` G ) P <-> P : ( 0 ... 0 ) --> V ) )

  proof
    cG
    cU
    wcel
    #
    c0
    cP
    cG
    cwlks
    cfv
    wbr
    #
    c0
    ccnv
    wfun
    #
    wa
    cc0
    cc0
    cfz
    co
    cV
    cP
    wf
    #
    @2
    wa
    c0
    cP
    cG
    ctrls
    cfv
    wbr
    @3
    @0
    @1
    @3
    @2
    cP
    cU
    cG
    cV
    0wlk.v
    0wlk
    anbi1d
    cP
    c0
    cG
    istrl
    @2
    @3
    funcnv0
    biantru
    3bitr4g
end
