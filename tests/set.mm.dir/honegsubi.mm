include "cv.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chos.mm"
include "cfv.mm"
include "chod.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cmv.mm"
include "cva.mm"
include "wf.mm"
include "cc.mm"
include "neg1cn.mm"
include "homulcl.mm"
include "mp2an.mm"
include "hosval.mm"
include "mp3an12.mm"
include "csm.mm"
include "ffvelrni.mm"
include "hvsubval.mm"
include "syl2anc.mm"
include "homval.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "hodval.mm"
include "rgen.mm"
include "hoaddcli.mm"
include "hosubcli.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem honegsubi
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hodseq.2: |- S : ~H --> ~H
  assume hodseq.3: |- T : ~H --> ~H


  assert |- ( S +op ( -u 1 .op T ) ) = ( S -op T )

  proof
    vx
    cv
    #
    cS
    c1
    cneg
    #
    cT
    chot
    co
    #
    chos
    co
    #
    cfv
    #
    @0
    cS
    cT
    chod
    co
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @3
    @5
    wceq
    @7
    vx
    chil
    @0
    chil
    wcel
    #
    @4
    @0
    cS
    cfv
    #
    @0
    cT
    cfv
    #
    cmv
    co
    #
    @6
    @8
    @4
    @9
    @0
    @2
    cfv
    #
    cva
    co
    #
    @11
    chil
    chil
    cS
    wf
    #
    chil
    chil
    @2
    wf
    #
    @8
    @4
    @13
    wceq
    hodseq.2
    @1
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    @15
    neg1cn
    hodseq.3
    @1
    cT
    homulcl
    mp2an
    #
    @0
    cS
    @2
    hosval
    mp3an12
    @8
    @11
    @9
    @1
    @10
    csm
    co
    #
    cva
    co
    #
    @13
    @8
    @9
    chil
    wcel
    @10
    chil
    wcel
    @11
    @20
    wceq
    chil
    chil
    @0
    cS
    hodseq.2
    ffvelrni
    chil
    chil
    @0
    cT
    hodseq.3
    ffvelrni
    @9
    @10
    hvsubval
    syl2anc
    @8
    @12
    @19
    @9
    cva
    @16
    @17
    @8
    @12
    @19
    wceq
    neg1cn
    hodseq.3
    @1
    @0
    cT
    homval
    mp3an12
    oveq2d
    eqtr4d
    eqtr4d
    @14
    @17
    @8
    @6
    @11
    wceq
    hodseq.2
    hodseq.3
    @0
    cS
    cT
    hodval
    mp3an12
    eqtr4d
    rgen
    vx
    @3
    @5
    cS
    @2
    hodseq.2
    @18
    hoaddcli
    cS
    cT
    hodseq.2
    hodseq.3
    hosubcli
    hoeqi
    mpbi
end
