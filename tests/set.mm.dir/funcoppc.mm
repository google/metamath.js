include "cbs.mm"
include "cfv.mm"
include "cco.mm"
include "ccid.mm"
include "ctpos.mm"
include "chom.mm"
include "eqid.mm"
include "oppcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "cop.mm"
include "cfunc.mm"
include "co.mm"
include "wa.mm"
include "wbr.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "oppccat.mm"
include "simprd.mm"
include "funcf1.mm"
include "cxp.mm"
include "wfn.mm"
include "funcfn2.mm"
include "tposfn.mm"
include "cv.mm"
include "wf.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "funcf2.mm"
include "ovtpos.mm"
include "feq1i.mm"
include "oppchom.mm"
include "feq23i.mm"
include "bitri.mm"
include "sylibr.mm"
include "simpr.mm"
include "funcid.mm"
include "wceq.mm"
include "a1i.mm"
include "oppcid.mm"
include "fveq1d.mm"
include "fveq12d.mm"
include "3eqtr4d.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp23.mm"
include "simp22.mm"
include "simp21.mm"
include "simp3r.mm"
include "syl6eleq.mm"
include "simp3l.mm"
include "funcco.mm"
include "oppcco.mm"
include "fveq2d.mm"
include "ffvelrnd.mm"
include "fveq1i.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "isfuncd.mm"

theorem funcoppc
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
  let cO: class O
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume funcoppc.o: |- O = ( oppCat ` C )
  assume funcoppc.p: |- P = ( oppCat ` D )
  assume funcoppc.f: |- ( ph -> F ( C Func D ) G )


  assert |- ( ph -> F ( O Func P ) tpos G )

  proof
    wph
    vx
    vy
    vz
    cC
    cbs
    cfv
    #
    cD
    cbs
    cfv
    #
    cO
    cO
    cco
    cfv
    #
    cO
    ccid
    cfv
    #
    vf
    vg
    cP
    cF
    cG
    ctpos
    #
    cO
    chom
    cfv
    #
    cP
    ccid
    cfv
    #
    cP
    chom
    cfv
    #
    cP
    cco
    cfv
    #
    @0
    cC
    cO
    funcoppc.o
    @0
    eqid
    #
    oppcbas
    @1
    cD
    cP
    funcoppc.p
    @1
    eqid
    #
    oppcbas
    @5
    eqid
    @7
    eqid
    @3
    eqid
    @6
    eqid
    @2
    eqid
    @8
    eqid
    wph
    cC
    ccat
    wcel
    #
    cO
    ccat
    wcel
    wph
    @11
    cD
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    @11
    @12
    wa
    wph
    cF
    cG
    @14
    wbr
    #
    @15
    funcoppc.f
    cF
    cG
    @14
    df-br
    sylib
    cC
    cD
    @13
    funcrcl
    syl
    #
    simpld
    #
    cC
    cO
    funcoppc.o
    oppccat
    syl
    wph
    @12
    cP
    ccat
    wcel
    wph
    @11
    @12
    @17
    simprd
    #
    cD
    cP
    funcoppc.p
    oppccat
    syl
    wph
    @0
    @1
    cC
    cD
    cF
    cG
    @9
    @10
    funcoppc.f
    funcf1
    #
    wph
    cG
    @0
    @0
    cxp
    #
    wfn
    @4
    @21
    wfn
    wph
    @0
    cC
    cD
    cF
    cG
    @9
    funcoppc.f
    funcfn2
    @0
    @0
    cG
    tposfn
    syl
    wph
    vx
    cv
    #
    @0
    wcel
    #
    vy
    cv
    #
    @0
    wcel
    #
    wa
    #
    wa
    #
    @24
    @22
    cC
    chom
    cfv
    #
    co
    #
    @24
    cF
    cfv
    #
    @22
    cF
    cfv
    #
    cD
    chom
    cfv
    #
    co
    #
    @24
    @22
    cG
    co
    #
    wf
    #
    @22
    @24
    @5
    co
    #
    @31
    @30
    @7
    co
    #
    @22
    @24
    @4
    co
    #
    wf
    #
    @27
    @0
    cC
    cD
    cF
    cG
    @28
    @32
    @24
    @22
    @9
    @28
    eqid
    #
    @32
    eqid
    #
    wph
    @16
    @26
    funcoppc.f
    adantr
    wph
    @23
    @25
    simprr
    wph
    @23
    @25
    simprl
    funcf2
    @39
    @36
    @37
    @34
    wf
    @35
    @36
    @37
    @38
    @34
    @22
    @24
    cG
    ovtpos
    #
    feq1i
    @36
    @37
    @29
    @33
    @34
    cC
    @28
    cO
    @22
    @24
    @40
    funcoppc.o
    oppchom
    #
    cD
    @32
    cP
    @31
    @30
    @41
    funcoppc.p
    oppchom
    feq23i
    bitri
    sylibr
    wph
    @23
    wa
    #
    @22
    cC
    ccid
    cfv
    #
    cfv
    #
    @22
    @22
    cG
    co
    #
    cfv
    @31
    cD
    ccid
    cfv
    #
    cfv
    @22
    @3
    cfv
    #
    @22
    @22
    @4
    co
    #
    cfv
    @31
    @6
    cfv
    @44
    @0
    cC
    @45
    cD
    cF
    cG
    @48
    @22
    @9
    @45
    eqid
    #
    @48
    eqid
    #
    wph
    @16
    @23
    funcoppc.f
    adantr
    wph
    @23
    simpr
    funcid
    @44
    @49
    @46
    @50
    @47
    @50
    @47
    wceq
    @44
    @22
    @22
    cG
    ovtpos
    a1i
    @44
    @22
    @3
    @45
    wph
    @3
    @45
    wceq
    #
    @23
    wph
    @11
    @53
    @18
    @45
    cC
    cO
    funcoppc.o
    @51
    oppcid
    syl
    adantr
    fveq1d
    fveq12d
    @44
    @31
    @6
    @48
    wph
    @6
    @48
    wceq
    #
    @23
    wph
    @12
    @54
    @19
    @48
    cD
    cP
    funcoppc.p
    @52
    oppcid
    syl
    adantr
    fveq1d
    3eqtr4d
    wph
    @23
    @25
    vz
    cv
    #
    @0
    wcel
    #
    w3a
    #
    vf
    cv
    #
    @36
    wcel
    #
    vg
    cv
    #
    @24
    @55
    @5
    co
    #
    wcel
    #
    wa
    #
    w3a
    #
    @60
    @58
    @22
    @24
    cop
    @55
    @2
    co
    co
    #
    @55
    @22
    cG
    co
    #
    cfv
    #
    @60
    @55
    @24
    cG
    co
    #
    cfv
    #
    @58
    @34
    cfv
    #
    @31
    @30
    cop
    @55
    cF
    cfv
    #
    @8
    co
    #
    co
    #
    @65
    @22
    @55
    @4
    co
    #
    cfv
    @60
    @24
    @55
    @4
    co
    #
    cfv
    #
    @58
    @38
    cfv
    #
    @72
    co
    @64
    @58
    @60
    @55
    @24
    cop
    @22
    cC
    cco
    cfv
    #
    co
    co
    #
    @66
    cfv
    @70
    @69
    @71
    @30
    cop
    @31
    cD
    cco
    cfv
    #
    co
    co
    @67
    @73
    @64
    @0
    cC
    @78
    cD
    cF
    cG
    @28
    @60
    @58
    @80
    @55
    @24
    @22
    @9
    @40
    @78
    eqid
    #
    @80
    eqid
    #
    wph
    @57
    @16
    @63
    funcoppc.f
    3ad2ant1
    wph
    @23
    @25
    @56
    @63
    simp23
    #
    wph
    @23
    @25
    @56
    @63
    simp22
    #
    wph
    @23
    @25
    @56
    @63
    simp21
    #
    @64
    @60
    @61
    @55
    @24
    @28
    co
    wph
    @57
    @59
    @62
    simp3r
    cC
    @28
    cO
    @24
    @55
    @40
    funcoppc.o
    oppchom
    syl6eleq
    @64
    @58
    @36
    @29
    wph
    @57
    @59
    @62
    simp3l
    @43
    syl6eleq
    funcco
    @64
    @65
    @79
    @66
    @64
    @0
    cC
    @78
    @58
    @60
    cO
    @22
    @24
    @55
    @9
    @81
    funcoppc.o
    @85
    @84
    @83
    oppcco
    fveq2d
    @64
    @1
    cD
    @80
    @70
    @69
    cP
    @31
    @30
    @71
    @10
    @82
    funcoppc.p
    @64
    @0
    @1
    @22
    cF
    wph
    @57
    @0
    @1
    cF
    wf
    @63
    @20
    3ad2ant1
    #
    @85
    ffvelrnd
    @64
    @0
    @1
    @24
    cF
    @86
    @84
    ffvelrnd
    @64
    @0
    @1
    @55
    cF
    @86
    @83
    ffvelrnd
    oppcco
    3eqtr4d
    @65
    @74
    @66
    @22
    @55
    cG
    ovtpos
    fveq1i
    @76
    @69
    @77
    @70
    @72
    @60
    @75
    @68
    @24
    @55
    cG
    ovtpos
    fveq1i
    @58
    @38
    @34
    @42
    fveq1i
    oveq12i
    3eqtr4g
    isfuncd
end
