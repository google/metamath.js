include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "ctrlson.mm"
include "wbr.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "0wlkon.mm"
include "simpl.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "0wlkonlem1.mm"
include "1vgrex.mm"
include "adantr.mm"
include "0trl.mm"
include "3syl.mm"
include "mpbird.mm"
include "cpm.mm"
include "0ex.mm"
include "a1i.mm"
include "0wlkonlem2.mm"
include "istrlson.mm"
include "syl12anc.mm"
include "mpbir2and.mm"

theorem 0trlon
  let cP: class P
  let cG: class G
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( ( P : ( 0 ... 0 ) --> V /\ ( P ` 0 ) = N ) -> (/) ( N ( TrailsOn ` G ) N ) P )

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
    ctrlson
    cfv
    co
    wbr
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
    ctrls
    cfv
    wbr
    #
    cP
    cG
    cN
    cV
    0wlk.v
    0wlkon
    @3
    @6
    @1
    @1
    @2
    simpl
    @3
    cN
    cV
    wcel
    #
    @7
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
    @7
    @9
    @7
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
    0trl
    3syl
    mpbird
    @3
    @8
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
    @4
    @5
    @6
    wa
    wb
    @10
    @11
    @3
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
    @12
    0wlk.v
    istrlson
    syl12anc
    mpbir2and
end
