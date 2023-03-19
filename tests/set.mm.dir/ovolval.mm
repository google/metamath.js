include "cr.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "covol.mm"
include "cfv.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "reex.mm"
include "elpw2.mm"
include "cv.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "csup.mm"
include "wa.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "syl6eqr.mm"
include "infeq1d.mm"
include "df-ovol.mm"
include "xrltso.mm"
include "infex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem ovolval
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cM: class M
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cS: class S
  assume ovolval.1: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }

  disjoint f y
  disjoint A f
  disjoint A y
  disjoint f x
  disjoint x y
  disjoint A x
  disjoint B f
  disjoint B y
  disjoint F f
  disjoint M x
  disjoint S f
  disjoint S y
  assert |- ( A C_ RR -> ( vol* ` A ) = inf ( M , RR* , < ) )

  proof
    cA
    cr
    wss
    cA
    cr
    cpw
    #
    wcel
    cA
    covol
    cfv
    cM
    cxr
    clt
    cinf
    #
    wceq
    cA
    cr
    reex
    elpw2
    vx
    cA
    vx
    cv
    #
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    #
    wss
    #
    vy
    cv
    caddc
    cabs
    cmin
    ccom
    @3
    ccom
    c1
    cseq
    crn
    cxr
    clt
    csup
    wceq
    #
    wa
    #
    vf
    cle
    cr
    cr
    cxp
    cin
    cn
    cmap
    co
    #
    wrex
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    @1
    @0
    covol
    @2
    cA
    wceq
    #
    cxr
    @10
    cM
    clt
    @11
    @10
    cA
    @4
    wss
    #
    @6
    wa
    #
    vf
    @8
    wrex
    #
    vy
    cxr
    crab
    cM
    @11
    @9
    @14
    vy
    cxr
    @11
    @7
    @13
    vf
    @8
    @11
    @5
    @12
    @6
    @2
    cA
    @4
    sseq1
    anbi1d
    rexbidv
    rabbidv
    ovolval.1
    syl6eqr
    infeq1d
    vx
    vy
    vf
    df-ovol
    cxr
    cM
    clt
    xrltso
    infex
    fvmpt
    sylbir
end
