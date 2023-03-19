include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cwlkson.mm"
include "wbr.mm"
include "cwlks.mm"
include "chash.mm"
include "simpl.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "0wlkonlem1.mm"
include "1vgrex.mm"
include "adantr.mm"
include "0wlk.mm"
include "3syl.mm"
include "mpbird.mm"
include "simpr.mm"
include "hash0.mm"
include "fveq2i.mm"
include "syl5eq.mm"
include "cpm.mm"
include "w3a.mm"
include "0ex.mm"
include "a1i.mm"
include "0wlkonlem2.mm"
include "iswlkon.mm"
include "syl12anc.mm"
include "mpbir3and.mm"

theorem 0wlkon
  let cP: class P
  let cG: class G
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( ( P : ( 0 ... 0 ) --> V /\ ( P ` 0 ) = N ) -> (/) ( N ( WalksOn ` G ) N ) P )

  proof
    cc0
    cc0
    cfz
    co
    #
    cV
    cP
    wf
    #
    cc0
    cP
    cfv
    #
    cN
    wceq
    #
    wa
    #
    c0
    cP
    cN
    cN
    cG
    cwlkson
    cfv
    co
    wbr
    #
    c0
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @3
    c0
    chash
    cfv
    #
    cP
    cfv
    #
    cN
    wceq
    #
    @4
    @6
    @1
    @1
    @3
    simpl
    @4
    cN
    cV
    wcel
    #
    @10
    wa
    #
    cG
    cvv
    wcel
    #
    @6
    @1
    wb
    cP
    cG
    cN
    cV
    0wlk.v
    0wlkonlem1
    #
    @10
    @12
    @10
    cG
    cN
    cV
    0wlk.v
    1vgrex
    adantr
    cP
    cvv
    cG
    cV
    0wlk.v
    0wlk
    3syl
    mpbird
    @1
    @3
    simpr
    #
    @4
    @8
    @2
    cN
    @7
    cc0
    cP
    hash0
    fveq2i
    @14
    syl5eq
    @4
    @11
    c0
    cvv
    wcel
    #
    cP
    cV
    @0
    cpm
    co
    #
    wcel
    @5
    @6
    @3
    @9
    w3a
    wb
    @13
    @15
    @4
    0ex
    a1i
    cP
    cG
    cN
    cV
    0wlk.v
    0wlkonlem2
    cN
    cN
    cP
    cvv
    c0
    cG
    cV
    @16
    0wlk.v
    iswlkon
    syl12anc
    mpbir3and
end
