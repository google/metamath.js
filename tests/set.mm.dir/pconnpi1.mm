include "cpconn.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cgic.mm"
include "wbr.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "pconncn.mm"
include "cpi1.mm"
include "cbs.mm"
include "cuni.mm"
include "cphtpc.mm"
include "cec.mm"
include "cicc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cpco.mm"
include "cop.mm"
include "crn.mm"
include "cgim.mm"
include "eqid.mm"
include "ctop.mm"
include "ctopon.mm"
include "simpl1.mm"
include "pconntop.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "simprl.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "pi1xfrgim.mm"
include "simprrl.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "simprrr.mm"
include "oveq12d.mm"
include "eleqtrd.mm"
include "brgici.mm"
include "rexlimddv.mm"

theorem pconnpi1
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume pconnpi1.x: |- X = U. J
  assume pconnpi1.p: |- P = ( J pi1 A )
  assume pconnpi1.q: |- Q = ( J pi1 B )
  assume pconnpi1.s: |- S = ( Base ` P )
  assume pconnpi1.t: |- T = ( Base ` Q )


  assert |- ( ( J e. PConn /\ A e. X /\ B e. X ) -> P ~=g Q )

  proof
    cJ
    cpconn
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cc0
    vf
    cv
    #
    cfv
    #
    cA
    wceq
    #
    c1
    @4
    cfv
    #
    cB
    wceq
    #
    wa
    #
    cP
    cQ
    cgic
    wbr
    #
    vf
    cii
    cJ
    ccn
    co
    #
    cA
    cB
    vf
    cJ
    cX
    pconnpi1.x
    pconncn
    @3
    @4
    @11
    wcel
    #
    @9
    wa
    #
    wa
    #
    vh
    cJ
    @5
    cpi1
    co
    #
    cbs
    cfv
    #
    cuni
    vh
    cv
    #
    cJ
    cphtpc
    cfv
    #
    cec
    vx
    cc0
    c1
    cicc
    co
    #
    c1
    vx
    cv
    #
    cmin
    co
    #
    @4
    cfv
    #
    cmpt
    #
    @17
    @4
    cJ
    cpco
    cfv
    #
    co
    @24
    co
    @18
    cec
    cop
    cmpt
    crn
    #
    cP
    cQ
    cgim
    co
    #
    wcel
    @10
    @14
    @25
    @15
    cJ
    @7
    cpi1
    co
    #
    cgim
    co
    @26
    @14
    vy
    @16
    @15
    @27
    vh
    @4
    @25
    @23
    cJ
    cX
    @15
    eqid
    @27
    eqid
    @16
    eqid
    @25
    eqid
    @14
    cJ
    ctop
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    @14
    @0
    @28
    @0
    @1
    @2
    @13
    simpl1
    cJ
    pconntop
    syl
    cJ
    cX
    pconnpi1.x
    toptopon
    sylib
    @3
    @12
    @9
    simprl
    vx
    vy
    @19
    @22
    c1
    vy
    cv
    #
    cmin
    co
    #
    @4
    cfv
    @20
    @29
    wceq
    @21
    @30
    @4
    @20
    @29
    c1
    cmin
    oveq2
    fveq2d
    cbvmptv
    pi1xfrgim
    @14
    @15
    cP
    @27
    cQ
    cgim
    @14
    @15
    cJ
    cA
    cpi1
    co
    cP
    @14
    @5
    cA
    cJ
    cpi1
    @3
    @12
    @6
    @8
    simprrl
    oveq2d
    pconnpi1.p
    syl6eqr
    @14
    @27
    cJ
    cB
    cpi1
    co
    cQ
    @14
    @7
    cB
    cJ
    cpi1
    @3
    @12
    @6
    @8
    simprrr
    oveq2d
    pconnpi1.q
    syl6eqr
    oveq12d
    eleqtrd
    cP
    cQ
    @25
    brgici
    syl
    rexlimddv
end
