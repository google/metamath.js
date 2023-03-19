include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cmap.mm"
include "crrx.mm"
include "cbs.mm"
include "k0004ss1.mm"
include "cv.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "wa.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "fzfid.mm"
include "0red.mm"
include "fdmfifsupp.mm"
include "ssrabdv.mm"
include "cvv.mm"
include "wceq.mm"
include "ovex.mm"
include "eqid.mm"
include "rrxbase.mm"
include "ax-mp.mm"
include "syl6sseqr.mm"
include "sstrd.mm"

theorem k0004ss2
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vv: setvar v
  assume k0004.a: |- A = ( n e. NN0 |-> { t e. ( ( 0 [,] 1 ) ^m ( 1 ... ( n + 1 ) ) ) | sum_ k e. ( 1 ... ( n + 1 ) ) ( t ` k ) = 1 } )

  disjoint k n
  disjoint n t
  disjoint N k
  disjoint N t
  disjoint N n
  disjoint N v
  assert |- ( N e. NN0 -> ( A ` N ) C_ ( Base ` ( RR^ ` ( 1 ... ( N + 1 ) ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cA
    cfv
    cr
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cmap
    co
    #
    @2
    crrx
    cfv
    #
    cbs
    cfv
    #
    vt
    cA
    vk
    vn
    cN
    k0004.a
    k0004ss1
    @0
    @3
    vv
    cv
    #
    cc0
    cfsupp
    wbr
    #
    vv
    @3
    crab
    #
    @5
    @0
    @7
    vv
    @3
    @3
    @3
    @3
    wss
    @0
    @3
    ssid
    a1i
    @0
    @6
    @3
    wcel
    #
    wa
    #
    @2
    cr
    @6
    cr
    cc0
    @9
    @2
    cr
    @6
    wf
    @0
    @6
    cr
    @2
    elmapi
    adantl
    @10
    c1
    @1
    fzfid
    @10
    0red
    fdmfifsupp
    ssrabdv
    @2
    cvv
    wcel
    @5
    @8
    wceq
    c1
    @1
    cfz
    ovex
    @5
    vv
    @4
    @2
    cvv
    @4
    eqid
    @5
    eqid
    rrxbase
    ax-mp
    syl6sseqr
    sstrd
end
