include "chos.mm"
include "co.mm"
include "clo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "lnopfi.mm"
include "hoaddcli.mm"
include "wa.mm"
include "hvmulcl.mm"
include "lnopaddi.mm"
include "oveq12d.mm"
include "sylan.mm"
include "ffvelrni.mm"
include "syl.mm"
include "anim12i.mm"
include "hvadd4.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "hvaddcl.mm"
include "hosval.mm"
include "mp3an12.mm"
include "jca.mm"
include "ax-hvdistr1.mm"
include "3expb.mm"
include "sylan2.mm"
include "oveq2d.mm"
include "adantl.mm"
include "lnopmuli.mm"
include "3eqtr4d.mm"
include "oveqan12d.mm"
include "ralrimiva.mm"
include "rgen2.mm"
include "ellnop.mm"
include "mpbir2an.mm"

theorem lnophsi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnopco.1: |- S e. LinOp
  assume lnopco.2: |- T e. LinOp


  assert |- ( S +op T ) e. LinOp

  proof
    cS
    cT
    chos
    co
    #
    clo
    wcel
    chil
    chil
    @0
    wf
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    @0
    cfv
    #
    @1
    @2
    @0
    cfv
    #
    csm
    co
    #
    @4
    @0
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    #
    vy
    chil
    wral
    vx
    cc
    wral
    cS
    cT
    cS
    lnopco.1
    lnopfi
    #
    cT
    lnopco.2
    lnopfi
    #
    hoaddcli
    @12
    vx
    vy
    cc
    chil
    @1
    cc
    wcel
    #
    @2
    chil
    wcel
    #
    wa
    #
    @11
    vz
    chil
    @17
    @4
    chil
    wcel
    #
    wa
    #
    @5
    cS
    cfv
    #
    @5
    cT
    cfv
    #
    cva
    co
    #
    @3
    cS
    cfv
    #
    @3
    cT
    cfv
    #
    cva
    co
    #
    @4
    cS
    cfv
    #
    @4
    cT
    cfv
    #
    cva
    co
    #
    cva
    co
    #
    @6
    @10
    @19
    @22
    @23
    @26
    cva
    co
    #
    @24
    @27
    cva
    co
    #
    cva
    co
    #
    @29
    @17
    @3
    chil
    wcel
    #
    @18
    @22
    @32
    wceq
    @1
    @2
    hvmulcl
    #
    @33
    @18
    wa
    @20
    @30
    @21
    @31
    cva
    @3
    @4
    cS
    lnopco.1
    lnopaddi
    @3
    @4
    cT
    lnopco.2
    lnopaddi
    oveq12d
    sylan
    @19
    @23
    chil
    wcel
    #
    @26
    chil
    wcel
    #
    wa
    @24
    chil
    wcel
    #
    @27
    chil
    wcel
    #
    wa
    @32
    @29
    wceq
    @17
    @35
    @18
    @36
    @17
    @33
    @35
    @34
    chil
    chil
    @3
    cS
    @13
    ffvelrni
    syl
    chil
    chil
    @4
    cS
    @13
    ffvelrni
    anim12i
    @17
    @37
    @18
    @38
    @17
    @33
    @37
    @34
    chil
    chil
    @3
    cT
    @14
    ffvelrni
    syl
    chil
    chil
    @4
    cT
    @14
    ffvelrni
    anim12i
    @23
    @26
    @24
    @27
    hvadd4
    syl2anc
    eqtrd
    @19
    @5
    chil
    wcel
    #
    @6
    @22
    wceq
    #
    @17
    @33
    @18
    @39
    @34
    @3
    @4
    hvaddcl
    sylan
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    @39
    @40
    @13
    @14
    @5
    cS
    cT
    hosval
    mp3an12
    syl
    @17
    @18
    @8
    @25
    @9
    @28
    cva
    @17
    @1
    @2
    cS
    cfv
    #
    @2
    cT
    cfv
    #
    cva
    co
    #
    csm
    co
    #
    @1
    @43
    csm
    co
    #
    @1
    @44
    csm
    co
    #
    cva
    co
    #
    @8
    @25
    @16
    @15
    @43
    chil
    wcel
    #
    @44
    chil
    wcel
    #
    wa
    @46
    @49
    wceq
    #
    @16
    @50
    @51
    chil
    chil
    @2
    cS
    @13
    ffvelrni
    chil
    chil
    @2
    cT
    @14
    ffvelrni
    jca
    @15
    @50
    @51
    @52
    @1
    @43
    @44
    ax-hvdistr1
    3expb
    sylan2
    @16
    @8
    @46
    wceq
    @15
    @16
    @7
    @45
    @1
    csm
    @41
    @42
    @16
    @7
    @45
    wceq
    @13
    @14
    @2
    cS
    cT
    hosval
    mp3an12
    oveq2d
    adantl
    @17
    @23
    @47
    @24
    @48
    cva
    @1
    @2
    cS
    lnopco.1
    lnopmuli
    @1
    @2
    cT
    lnopco.2
    lnopmuli
    oveq12d
    3eqtr4d
    @41
    @42
    @18
    @9
    @28
    wceq
    @13
    @14
    @4
    cS
    cT
    hosval
    mp3an12
    oveqan12d
    3eqtr4d
    ralrimiva
    rgen2
    vx
    vy
    vz
    @0
    ellnop
    mpbir2an
end
