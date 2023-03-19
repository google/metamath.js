include "wceq.mm"
include "ctpos.mm"
include "wss.mm"
include "eqimss.mm"
include "tposss.mm"
include "syl.mm"
include "eqimss2.mm"
include "eqssd.mm"

theorem tposeq
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z


  assert |- ( F = G -> tpos F = tpos G )

  proof
    cF
    cG
    wceq
    #
    cF
    ctpos
    #
    cG
    ctpos
    #
    @0
    cF
    cG
    wss
    @1
    @2
    wss
    cF
    cG
    eqimss
    cF
    cG
    tposss
    syl
    @0
    cG
    cF
    wss
    @2
    @1
    wss
    cG
    cF
    eqimss2
    cG
    cF
    tposss
    syl
    eqssd
end
