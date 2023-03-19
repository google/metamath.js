include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "dmsnopg.mm"
include "eqimss.mm"
include "syl.mm"
include "wn.mm"
include "c0.mm"
include "opprc2.mm"
include "sneqd.mm"
include "dmeqd.mm"
include "dmsn0.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem dmsnopss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- dom { <. A , B >. } C_ { A }

  proof
    cB
    cvv
    wcel
    #
    cA
    cB
    cop
    #
    csn
    #
    cdm
    #
    cA
    csn
    #
    wss
    #
    @0
    @3
    @4
    wceq
    @5
    cA
    cB
    cvv
    dmsnopg
    @3
    @4
    eqimss
    syl
    @0
    wn
    #
    @3
    c0
    @4
    @6
    @3
    c0
    csn
    #
    cdm
    c0
    @6
    @2
    @7
    @6
    @1
    c0
    cA
    cB
    opprc2
    sneqd
    dmeqd
    dmsn0
    syl6eq
    @4
    0ss
    syl6eqss
    pm2.61i
end
