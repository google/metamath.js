include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "cin.mm"
include "cuni.mm"
include "cmpt.mm"
include "wceq.mm"
include "ntrfval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "wb.mm"
include "topopn.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "inex1g.mm"
include "uniexg.mm"
include "pweq.mm"
include "ineq2d.mm"
include "unieqd.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem ntrval
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume iscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( int ` J ) ` S ) = U. ( J i^i ~P S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cJ
    cnt
    cfv
    #
    cfv
    #
    cS
    vx
    cX
    cpw
    #
    cJ
    vx
    cv
    #
    cpw
    #
    cin
    #
    cuni
    #
    cmpt
    #
    cfv
    #
    cJ
    cS
    cpw
    #
    cin
    #
    cuni
    #
    @0
    @4
    @11
    wceq
    @1
    @0
    cS
    @3
    @10
    vx
    cJ
    cX
    iscld.1
    ntrfval
    fveq1d
    adantr
    @2
    cS
    @5
    wcel
    #
    @14
    cvv
    wcel
    #
    @11
    @14
    wceq
    @0
    @15
    @1
    @0
    cX
    cJ
    wcel
    @15
    @1
    wb
    cJ
    cX
    iscld.1
    topopn
    cS
    cX
    cJ
    elpw2g
    syl
    biimpar
    @2
    @13
    cvv
    wcel
    #
    @16
    @0
    @17
    @1
    cJ
    @12
    ctop
    inex1g
    adantr
    @13
    cvv
    uniexg
    syl
    vx
    cS
    @9
    @14
    @5
    cvv
    @10
    @6
    cS
    wceq
    #
    @8
    @13
    @18
    @7
    @12
    cJ
    @6
    cS
    pweq
    ineq2d
    unieqd
    @10
    eqid
    fvmptg
    syl2anc
    eqtrd
end
