include "wcel.mm"
include "wa.mm"
include "crngs.mm"
include "co.mm"
include "crngh.mm"
include "ccnv.mm"
include "wf1o.mm"
include "isrngisom.mm"
include "wb.mm"
include "wi.mm"
include "rnghmf1o.mm"
include "bicomd.mm"
include "a1i.mm"
include "pm5.32d.mm"
include "bitrd.mm"

theorem isrngim
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume rnghmf1o.b: |- B = ( Base ` R )
  assume rnghmf1o.c: |- C = ( Base ` S )


  assert |- ( ( R e. V /\ S e. W ) -> ( F e. ( R RngIsom S ) <-> ( F e. ( R RngHomo S ) /\ F : B -1-1-onto-> C ) ) )

  proof
    cR
    cV
    wcel
    cS
    cW
    wcel
    wa
    #
    cF
    cR
    cS
    crngs
    co
    wcel
    cF
    cR
    cS
    crngh
    co
    wcel
    #
    cF
    ccnv
    cS
    cR
    crngh
    co
    wcel
    #
    wa
    @1
    cB
    cC
    cF
    wf1o
    #
    wa
    cR
    cS
    cF
    cV
    cW
    isrngisom
    @0
    @1
    @2
    @3
    @1
    @2
    @3
    wb
    wi
    @0
    @1
    @3
    @2
    cB
    cC
    cR
    cS
    cF
    rnghmf1o.b
    rnghmf1o.c
    rnghmf1o
    bicomd
    a1i
    pm5.32d
    bitrd
end
