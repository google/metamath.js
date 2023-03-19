include "cv.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cnop.mm"
include "wcel.mm"
include "csm.mm"
include "cc.mm"
include "wf.mm"
include "neg1cn.mm"
include "homval.mm"
include "mp3an12.mm"
include "fveq2d.mm"
include "ffvelrni.mm"
include "normneg.mm"
include "syl.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbiia.mm"
include "abbii.mm"
include "supeq1i.mm"
include "homulcl.mm"
include "mp2an.mm"
include "nmopval.mm"
include "ax-mp.mm"
include "3eqtr4i.mm"

theorem nmopnegi
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmopneg.1: |- T : ~H --> ~H


  assert |- ( normop ` ( -u 1 .op T ) ) = ( normop ` T )

  proof
    vy
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @0
    c1
    cneg
    #
    cT
    chot
    co
    #
    cfv
    #
    cno
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    @1
    @2
    @0
    cT
    cfv
    #
    cno
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    @4
    cnop
    cfv
    #
    cT
    cnop
    cfv
    #
    cxr
    @10
    @17
    clt
    @9
    @16
    vx
    @8
    @15
    vy
    chil
    @0
    chil
    wcel
    #
    @7
    @14
    @1
    @21
    @6
    @13
    @2
    @21
    @6
    @3
    @12
    csm
    co
    #
    cno
    cfv
    #
    @13
    @21
    @5
    @22
    cno
    @3
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    @21
    @5
    @22
    wceq
    neg1cn
    nmopneg.1
    @3
    @0
    cT
    homval
    mp3an12
    fveq2d
    @21
    @12
    chil
    wcel
    @23
    @13
    wceq
    chil
    chil
    @0
    cT
    nmopneg.1
    ffvelrni
    @12
    normneg
    syl
    eqtrd
    eqeq2d
    anbi2d
    rexbiia
    abbii
    supeq1i
    chil
    chil
    @4
    wf
    #
    @19
    @11
    wceq
    @24
    @25
    @26
    neg1cn
    nmopneg.1
    @3
    cT
    homulcl
    mp2an
    vx
    vy
    @4
    nmopval
    ax-mp
    @25
    @20
    @18
    wceq
    nmopneg.1
    vx
    vy
    cT
    nmopval
    ax-mp
    3eqtr4i
end
