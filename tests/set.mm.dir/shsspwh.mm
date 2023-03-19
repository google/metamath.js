include "csh.mm"
include "cuni.mm"
include "cpw.mm"
include "chil.mm"
include "pwuni.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "wceq.mm"
include "helsh.mm"
include "shss.mm"
include "rgen.mm"
include "ssunieq.mm"
include "mp2an.mm"
include "pweqi.mm"
include "sseqtr4i.mm"

theorem shsspwh
  let vx: setvar x


  assert |- SH C_ ~P ~H

  proof
    csh
    csh
    cuni
    #
    cpw
    chil
    cpw
    csh
    pwuni
    chil
    @0
    chil
    csh
    wcel
    vx
    cv
    #
    chil
    wss
    #
    vx
    csh
    wral
    chil
    @0
    wceq
    helsh
    @2
    vx
    csh
    @1
    shss
    rgen
    vx
    chil
    csh
    ssunieq
    mp2an
    pweqi
    sseqtr4i
end
