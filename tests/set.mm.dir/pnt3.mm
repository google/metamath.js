include "cv.mm"
include "crp.mm"
include "cchp.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cdiv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "c1.mm"
include "crli.mm"
include "eqid.mm"
include "pntrmax.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "cmul.mm"
include "caddc.mm"
include "cicc.mm"
include "cpnf.mm"
include "cioo.mm"
include "ce.mm"
include "cico.mm"
include "cc0.mm"
include "pntibnd.mm"
include "c3.mm"
include "c2.mm"
include "cdc.mm"
include "cexp.mm"
include "simpll.mm"
include "simplr.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr.mm"
include "breq2.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "breq1.mm"
include "breq2d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "ralbii.mm"
include "pntleml.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpi.mm"
include "rexlimiva.mm"
include "ax-mp.mm"

theorem pnt3
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vl: setvar l
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( x e. RR+ |-> ( ( psi ` x ) / x ) ) ~~>r 1

  proof
    vr
    cv
    #
    va
    crp
    va
    cv
    #
    cchp
    cfv
    @1
    cmin
    co
    cmpt
    #
    cfv
    #
    @0
    cdiv
    co
    #
    cabs
    cfv
    #
    vb
    cv
    #
    cle
    wbr
    #
    vr
    crp
    wral
    #
    vb
    crp
    wrex
    vx
    crp
    vx
    cv
    #
    cchp
    cfv
    @9
    cdiv
    co
    cmpt
    c1
    crli
    wbr
    #
    vr
    @2
    va
    vb
    @2
    eqid
    #
    pntrmax
    @8
    @10
    vb
    crp
    @6
    crp
    wcel
    #
    @8
    wa
    #
    vy
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    c1
    vl
    cv
    #
    ve
    cv
    #
    cmul
    co
    caddc
    co
    #
    @15
    cmul
    co
    #
    vk
    cv
    #
    @14
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    vu
    cv
    #
    @2
    cfv
    @25
    cdiv
    co
    cabs
    cfv
    @18
    cle
    wbr
    #
    vu
    @15
    @20
    cicc
    co
    #
    wral
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    @0
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    vc
    cv
    #
    @18
    cdiv
    co
    ce
    cfv
    cpnf
    cico
    co
    #
    wral
    #
    vr
    crp
    wrex
    #
    ve
    cc0
    c1
    cioo
    co
    #
    wral
    #
    vl
    @37
    wrex
    vc
    crp
    wrex
    @10
    vr
    vy
    vz
    vu
    @2
    ve
    vk
    va
    vc
    vl
    @11
    pntibnd
    @13
    @38
    @10
    vc
    vl
    crp
    @37
    @13
    @33
    crp
    wcel
    #
    @17
    @37
    wcel
    #
    wa
    #
    @38
    @10
    @13
    @41
    @38
    wa
    #
    wa
    #
    vx
    vf
    vg
    vu
    @6
    @33
    @6
    c1
    caddc
    co
    #
    @2
    ve
    vk
    c1
    c1
    @44
    cdiv
    co
    cmin
    co
    @17
    c3
    c2
    cdc
    @33
    cmul
    co
    cdiv
    co
    @44
    c2
    cexp
    co
    cdiv
    co
    cmul
    co
    #
    @17
    va
    @11
    @12
    @8
    @42
    simpll
    @43
    @8
    @9
    @2
    cfv
    #
    @9
    cdiv
    co
    #
    cabs
    cfv
    #
    @6
    cle
    wbr
    #
    vx
    crp
    wral
    @12
    @8
    @42
    simplr
    @7
    @49
    vr
    vx
    crp
    vr
    vx
    weq
    #
    @5
    @48
    @6
    cle
    @50
    @4
    @47
    cabs
    @50
    @3
    @46
    @0
    @9
    cdiv
    @0
    @9
    @2
    fveq2
    @50
    id
    oveq12d
    fveq2d
    breq1d
    cbvralv
    sylib
    @13
    @39
    @40
    @38
    simprll
    @13
    @39
    @40
    @38
    simprlr
    @44
    eqid
    @45
    eqid
    @43
    @38
    vf
    cv
    #
    vg
    cv
    #
    clt
    wbr
    #
    @19
    @52
    cmul
    co
    #
    @21
    @51
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    @26
    vu
    @52
    @54
    cicc
    co
    #
    wral
    #
    wa
    #
    vg
    crp
    wrex
    #
    vf
    @9
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    @34
    wral
    #
    vx
    crp
    wrex
    #
    ve
    @37
    wral
    @13
    @41
    @38
    simprr
    @36
    @65
    ve
    @37
    @35
    @64
    vr
    vx
    crp
    @50
    @32
    @63
    vk
    @34
    @32
    @61
    vf
    @31
    wral
    @50
    @63
    @30
    @61
    vy
    vf
    @31
    @30
    @14
    @52
    clt
    wbr
    #
    @54
    @22
    clt
    wbr
    #
    wa
    #
    @59
    wa
    #
    vg
    crp
    wrex
    vy
    vf
    weq
    #
    @61
    @29
    @69
    vz
    vg
    crp
    vz
    vg
    weq
    #
    @24
    @68
    @28
    @59
    @71
    @16
    @66
    @23
    @67
    @15
    @52
    @14
    clt
    breq2
    @71
    @20
    @54
    @22
    clt
    @15
    @52
    @19
    cmul
    oveq2
    #
    breq1d
    anbi12d
    @71
    @26
    vu
    @27
    @58
    @71
    @15
    @52
    @20
    @54
    cicc
    @71
    id
    @72
    oveq12d
    raleqdv
    anbi12d
    cbvrexv
    @70
    @69
    @60
    vg
    crp
    @70
    @68
    @57
    @59
    @70
    @66
    @53
    @67
    @56
    @14
    @51
    @52
    clt
    breq1
    @70
    @22
    @55
    @54
    clt
    @14
    @51
    @21
    cmul
    oveq2
    breq2d
    anbi12d
    anbi1d
    rexbidv
    syl5bb
    cbvralv
    @50
    @61
    vf
    @31
    @62
    @0
    @9
    cpnf
    cioo
    oveq1
    raleqdv
    syl5bb
    ralbidv
    cbvrexv
    ralbii
    sylib
    pntleml
    expr
    rexlimdvva
    mpi
    rexlimiva
    ax-mp
end
