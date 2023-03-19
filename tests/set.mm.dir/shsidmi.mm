include "cph.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "shseli.mm"
include "wa.mm"
include "csh.mm"
include "shaddcl.mm"
include "mp3an1.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"
include "shsub1i.mm"
include "eqssi.mm"

theorem shsidmi
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shsidm.1: |- A e. SH


  assert |- ( A +H A ) = A

  proof
    cA
    cA
    cph
    co
    #
    cA
    vx
    @0
    cA
    vx
    cv
    #
    @0
    wcel
    @1
    vy
    cv
    #
    vz
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    cA
    wrex
    vy
    cA
    wrex
    @1
    cA
    wcel
    #
    vy
    vz
    cA
    cA
    @1
    shsidm.1
    shsidm.1
    shseli
    @5
    @6
    vy
    vz
    cA
    cA
    @2
    cA
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    @6
    @5
    @4
    cA
    wcel
    #
    cA
    csh
    wcel
    @7
    @8
    @9
    shsidm.1
    @2
    @3
    cA
    shaddcl
    mp3an1
    @1
    @4
    cA
    eleq1
    syl5ibrcom
    rexlimivv
    sylbi
    ssriv
    cA
    cA
    shsidm.1
    shsidm.1
    shsub1i
    eqssi
end
