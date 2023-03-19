include "ccphlo.mm"
include "wcel.mm"
include "cnv.mm"
include "wfun.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "caj.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "syl5eq.mm"
include "funeqd.mm"
include "oveq2.mm"
include "eqid.mm"
include "elimphu.mm"
include "elimnvu.mm"
include "ajfuni.mm"
include "dedth2h.mm"

theorem ajfun
  let cA: class A
  let cU: class U
  let cW: class W
  assume ajfun.5: |- A = ( U adj W )


  assert |- ( ( U e. CPreHilOLD /\ W e. NrmCVec ) -> Fun A )

  proof
    cU
    ccphlo
    wcel
    #
    cW
    cnv
    wcel
    #
    cA
    wfun
    @0
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    cif
    #
    cW
    caj
    co
    #
    wfun
    @3
    @1
    cW
    @2
    cif
    #
    caj
    co
    #
    wfun
    cU
    cW
    @2
    @2
    cU
    @3
    wceq
    #
    cA
    @4
    @7
    cA
    cU
    cW
    caj
    co
    @4
    ajfun.5
    cU
    @3
    cW
    caj
    oveq1
    syl5eq
    funeqd
    cW
    @5
    wceq
    @4
    @6
    cW
    @5
    @3
    caj
    oveq2
    funeqd
    @6
    @3
    @5
    @6
    eqid
    cU
    elimphu
    cW
    elimnvu
    ajfuni
    dedth2h
end
