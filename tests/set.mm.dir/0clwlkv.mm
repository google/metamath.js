include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "csn.mm"
include "wf.mm"
include "w3a.mm"
include "cclwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cfz.mm"
include "co.mm"
include "fz0sn.mm"
include "eqcomi.mm"
include "feq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "wss.mm"
include "snssi.mm"
include "3ad2ant1.mm"
include "fssd.mm"
include "wb.mm"
include "breq1.mm"
include "3ad2ant2.mm"
include "cvv.mm"
include "1vgrex.mm"
include "0clwlk.mm"
include "syl.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem 0clwlkv
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  assume 0clwlk.v: |- V = ( Vtx ` G )


  assert |- ( ( X e. V /\ F = (/) /\ P : { 0 } --> { X } ) -> F ( ClWalks ` G ) P )

  proof
    cX
    cV
    wcel
    #
    cF
    c0
    wceq
    #
    cc0
    csn
    #
    cX
    csn
    #
    cP
    wf
    #
    w3a
    #
    cF
    cP
    cG
    cclwlks
    cfv
    #
    wbr
    #
    cc0
    cc0
    cfz
    co
    #
    cV
    cP
    wf
    #
    @5
    @8
    @3
    cV
    cP
    @4
    @0
    @8
    @3
    cP
    wf
    #
    @1
    @4
    @10
    @2
    @8
    @3
    cP
    @8
    @2
    fz0sn
    eqcomi
    feq2i
    biimpi
    3ad2ant3
    @0
    @1
    @3
    cV
    wss
    @4
    cX
    cV
    snssi
    3ad2ant1
    fssd
    @5
    @7
    c0
    cP
    @6
    wbr
    #
    @9
    @1
    @0
    @7
    @11
    wb
    @4
    cF
    c0
    cP
    @6
    breq1
    3ad2ant2
    @0
    @1
    @11
    @9
    wb
    #
    @4
    @0
    cG
    cvv
    wcel
    @12
    cG
    cX
    cV
    0clwlk.v
    1vgrex
    cP
    cG
    cV
    cvv
    0clwlk.v
    0clwlk
    syl
    3ad2ant1
    bitrd
    mpbird
end
