include "wceq.mm"
include "cop.mm"
include "csn.mm"
include "opeq2.mm"
include "sneqd.mm"
include "syl6reqr.mm"
include "w3a.mm"
include "eqid.mm"
include "3pm3.2i.mm"
include "eqeq1.mm"
include "snex.mm"
include "snopeqop.mm"
include "syl6bb.mm"
include "mpbiri.mm"
include "syl.mm"

theorem funsneqopsn
  let cA: class A
  let cB: class B
  let cG: class G
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume funsndifnop.a: |- A e. _V
  assume funsndifnop.b: |- B e. _V
  assume funsndifnop.g: |- G = { <. A , B >. }


  assert |- ( A = B -> G = <. { A } , { A } >. )

  proof
    cA
    cB
    wceq
    #
    cG
    cA
    cA
    cop
    #
    csn
    #
    wceq
    #
    cG
    cA
    csn
    #
    @4
    cop
    #
    wceq
    #
    @0
    @2
    cA
    cB
    cop
    #
    csn
    cG
    @0
    @1
    @7
    cA
    cB
    cA
    opeq2
    sneqd
    funsndifnop.g
    syl6reqr
    @3
    @6
    cA
    cA
    wceq
    #
    @4
    @4
    wceq
    #
    @9
    w3a
    #
    @8
    @9
    @9
    cA
    eqid
    @4
    eqid
    #
    @11
    3pm3.2i
    @3
    @6
    @2
    @5
    wceq
    @10
    cG
    @2
    @5
    eqeq1
    cA
    cA
    @4
    @4
    funsndifnop.a
    funsndifnop.a
    cA
    snex
    #
    @12
    snopeqop
    syl6bb
    mpbiri
    syl
end
