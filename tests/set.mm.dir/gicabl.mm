include "cgic.mm"
include "wbr.mm"
include "cgim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cabl.mm"
include "wcel.mm"
include "wb.mm"
include "brgic.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "cgrp.mm"
include "ccmn.mm"
include "wa.mm"
include "cghm.mm"
include "gimghm.mm"
include "ghmgrp1.mm"
include "syl.mm"
include "ghmgrp2.mm"
include "2thd.mm"
include "cmnd.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "grpmnd.mm"
include "wf1.mm"
include "wf1o.mm"
include "eqid.mm"
include "gimf1o.mm"
include "f1of1.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "ghmlin.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "2ralbidva.mm"
include "cima.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "raleqdv.mm"
include "wfn.mm"
include "wss.mm"
include "f1ofn.mm"
include "ssid.mm"
include "oveq2.mm"
include "oveq1.mm"
include "ralima.mm"
include "sylancl.mm"
include "ralbidv.mm"
include "bitr4d.mm"
include "anbi12d.mm"
include "iscmn.mm"
include "3bitr4g.mm"
include "isabl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem gicabl
  let cG: class G
  let cH: class H
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( G ~=g H -> ( G e. Abel <-> H e. Abel ) )

  proof
    cG
    cH
    cgic
    wbr
    cG
    cH
    cgim
    co
    #
    c0
    wne
    #
    cG
    cabl
    wcel
    #
    cH
    cabl
    wcel
    #
    wb
    #
    cG
    cH
    brgic
    @1
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @4
    vx
    @0
    n0
    @6
    @4
    vx
    @6
    cG
    cgrp
    wcel
    #
    cG
    ccmn
    wcel
    #
    wa
    cH
    cgrp
    wcel
    #
    cH
    ccmn
    wcel
    #
    wa
    @2
    @3
    @6
    @7
    @9
    @8
    @10
    @6
    @7
    @9
    @6
    @5
    cG
    cH
    cghm
    co
    wcel
    #
    @7
    cG
    cH
    @5
    gimghm
    #
    cG
    cH
    @5
    ghmgrp1
    syl
    #
    @6
    @11
    @9
    @12
    cG
    cH
    @5
    ghmgrp2
    syl
    #
    2thd
    @6
    cG
    cmnd
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @17
    @16
    @18
    co
    #
    wceq
    #
    vz
    cG
    cbs
    cfv
    #
    wral
    vy
    @22
    wral
    #
    wa
    cH
    cmnd
    wcel
    #
    vw
    cv
    #
    vv
    cv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    @26
    @25
    @27
    co
    #
    wceq
    #
    vv
    cH
    cbs
    cfv
    #
    wral
    #
    vw
    @31
    wral
    #
    wa
    @8
    @10
    @6
    @15
    @24
    @23
    @33
    @6
    @15
    @24
    @6
    @7
    @15
    @13
    cG
    grpmnd
    syl
    @6
    @9
    @24
    @14
    cH
    grpmnd
    syl
    2thd
    @6
    @23
    @16
    @5
    cfv
    #
    @26
    @27
    co
    #
    @26
    @34
    @27
    co
    #
    wceq
    #
    vv
    @31
    wral
    #
    vy
    @22
    wral
    #
    @33
    @6
    @23
    @34
    @17
    @5
    cfv
    #
    @27
    co
    #
    @40
    @34
    @27
    co
    #
    wceq
    #
    vz
    @22
    wral
    #
    vy
    @22
    wral
    @39
    @6
    @21
    @43
    vy
    vz
    @22
    @22
    @6
    @16
    @22
    wcel
    #
    @17
    @22
    wcel
    #
    wa
    #
    wa
    #
    @19
    @5
    cfv
    #
    @20
    @5
    cfv
    #
    wceq
    #
    @21
    @43
    @48
    @22
    @31
    @5
    wf1
    #
    @19
    @22
    wcel
    #
    @20
    @22
    wcel
    #
    @51
    @21
    wb
    @6
    @52
    @47
    @6
    @22
    @31
    @5
    wf1o
    #
    @52
    @22
    @31
    cG
    cH
    @5
    @22
    eqid
    #
    @31
    eqid
    #
    gimf1o
    #
    @22
    @31
    @5
    f1of1
    syl
    adantr
    @48
    @7
    @45
    @46
    @53
    @6
    @7
    @47
    @13
    adantr
    #
    @6
    @45
    @46
    simprl
    #
    @6
    @45
    @46
    simprr
    #
    @22
    @18
    cG
    @16
    @17
    @56
    @18
    eqid
    #
    grpcl
    syl3anc
    @48
    @7
    @46
    @45
    @54
    @59
    @61
    @60
    @22
    @18
    cG
    @17
    @16
    @56
    @62
    grpcl
    syl3anc
    @22
    @31
    @19
    @20
    @5
    f1fveq
    syl12anc
    @48
    @49
    @41
    @50
    @42
    @48
    @11
    @45
    @46
    @49
    @41
    wceq
    @6
    @11
    @47
    @12
    adantr
    #
    @60
    @61
    @18
    @27
    cG
    cH
    @16
    @5
    @17
    @22
    @56
    @62
    @27
    eqid
    #
    ghmlin
    syl3anc
    @48
    @11
    @46
    @45
    @50
    @42
    wceq
    @63
    @61
    @60
    @18
    @27
    cG
    cH
    @17
    @5
    @16
    @22
    @56
    @62
    @64
    ghmlin
    syl3anc
    eqeq12d
    bitr3d
    2ralbidva
    @6
    @38
    @44
    vy
    @22
    @6
    @37
    vv
    @5
    @22
    cima
    #
    wral
    #
    @38
    @44
    @6
    @37
    vv
    @65
    @31
    @6
    @55
    @65
    @31
    wceq
    #
    @58
    @55
    @22
    @31
    @5
    wfo
    @67
    @22
    @31
    @5
    f1ofo
    @22
    @31
    @5
    foima
    syl
    syl
    #
    raleqdv
    @6
    @5
    @22
    wfn
    #
    @22
    @22
    wss
    #
    @66
    @44
    wb
    @6
    @55
    @69
    @58
    @22
    @31
    @5
    f1ofn
    syl
    #
    @22
    ssid
    #
    @37
    @43
    vv
    vz
    @22
    @22
    @5
    @26
    @40
    wceq
    @35
    @41
    @36
    @42
    @26
    @40
    @34
    @27
    oveq2
    @26
    @40
    @34
    @27
    oveq1
    eqeq12d
    ralima
    sylancl
    bitr3d
    ralbidv
    bitr4d
    @6
    @32
    vw
    @65
    wral
    #
    @33
    @39
    @6
    @32
    vw
    @65
    @31
    @68
    raleqdv
    @6
    @69
    @70
    @73
    @39
    wb
    @71
    @72
    @32
    @38
    vw
    vy
    @22
    @22
    @5
    @25
    @34
    wceq
    #
    @30
    @37
    vv
    @31
    @74
    @28
    @35
    @29
    @36
    @25
    @34
    @26
    @27
    oveq1
    @25
    @34
    @26
    @27
    oveq2
    eqeq12d
    ralbidv
    ralima
    sylancl
    bitr3d
    bitr4d
    anbi12d
    vy
    vz
    @22
    @18
    cG
    @56
    @62
    iscmn
    vw
    vv
    @31
    @27
    cH
    @57
    @64
    iscmn
    3bitr4g
    anbi12d
    cG
    isabl
    cH
    isabl
    3bitr4g
    exlimiv
    sylbi
    sylbi
end
