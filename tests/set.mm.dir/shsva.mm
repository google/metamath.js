include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "cph.mm"
include "csh.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "rspceov.mm"
include "mp3an3.mm"
include "shsel.mm"
include "syl5ibr.mm"

theorem shsva
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. SH /\ B e. SH ) -> ( ( C e. A /\ D e. B ) -> ( C +h D ) e. ( A +H B ) ) )

  proof
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    wa
    cC
    cD
    cva
    co
    #
    cA
    cB
    cph
    co
    wcel
    cA
    csh
    wcel
    cB
    csh
    wcel
    wa
    @2
    vx
    cv
    vy
    cv
    cva
    co
    wceq
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @0
    @1
    @2
    @2
    wceq
    @3
    @2
    eqid
    vx
    vy
    cA
    cB
    cC
    cD
    @2
    cva
    rspceov
    mp3an3
    vx
    vy
    cA
    cB
    @2
    shsel
    syl5ibr
end
