include "ch0o.mm"
include "wne.mm"
include "cv.mm"
include "cleo.mm"
include "wbr.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cho.mm"
include "wrex.mm"
include "wcel.mm"
include "cnop.mm"
include "cfv.mm"
include "csqrt.mm"
include "chot.mm"
include "co.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "chil.mm"
include "wf.mm"
include "hmopf.mm"
include "ax-mp.mm"
include "nmopge0.mm"
include "sqrtcli.mm"
include "hmopm.mm"
include "mpan.mm"
include "ad2antlr.mm"
include "sqrtge0i.mm"
include "leopmuli.mm"
include "mpanr1.mm"
include "mpanl1.mm"
include "ad2ant2lr.mm"
include "cc.mm"
include "recni.mm"
include "homulcl.mm"
include "syl.mm"
include "homco1.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "clo.mm"
include "hmoplin.mm"
include "homco2.mm"
include "oveq2d.mm"
include "cmul.mm"
include "sqrtthi.mm"
include "oveq1i.mm"
include "fco.mm"
include "homulass.mm"
include "mp3an12.mm"
include "syl5reqr.mm"
include "3eqtrd.mm"
include "c1.mm"
include "cdiv.mm"
include "id.mm"
include "syl6eq.mm"
include "wb.mm"
include "nmlnopne0.mm"
include "recidzi.mm"
include "sylbir.mm"
include "oveq1d.mm"
include "rerecclzi.mm"
include "recnd.mm"
include "mp3an13.mm"
include "homulid2.mm"
include "mp1i.mm"
include "3eqtr3d.mm"
include "sylan9eqr.mm"
include "adantlr.mm"
include "eqtrd.mm"
include "adantrl.mm"
include "breq2.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "r19.29a.mm"

theorem opsqrlem1
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let cT: class T
  assume opsqrlem1.1: |- T e. HrmOp
  assume opsqrlem1.2: |- ( normop ` T ) e. RR
  assume opsqrlem1.3: |- 0hop <_op T
  assume opsqrlem1.4: |- R = ( ( 1 / ( normop ` T ) ) .op T )
  assume opsqrlem1.5: |- ( T =/= 0hop -> E. u e. HrmOp ( 0hop <_op u /\ ( u o. u ) = R ) )

  disjoint u v
  disjoint T u
  disjoint T v
  assert |- ( T =/= 0hop -> E. v e. HrmOp ( 0hop <_op v /\ ( v o. v ) = T ) )

  proof
    cT
    ch0o
    wne
    #
    ch0o
    vu
    cv
    #
    cleo
    wbr
    #
    @1
    @1
    ccom
    #
    cR
    wceq
    #
    wa
    #
    ch0o
    vv
    cv
    #
    cleo
    wbr
    #
    @6
    @6
    ccom
    #
    cT
    wceq
    #
    wa
    #
    vv
    cho
    wrex
    #
    vu
    cho
    @0
    @1
    cho
    wcel
    #
    wa
    #
    @5
    wa
    cT
    cnop
    cfv
    #
    csqrt
    cfv
    #
    @1
    chot
    co
    #
    cho
    wcel
    #
    ch0o
    @16
    cleo
    wbr
    #
    @16
    @16
    ccom
    #
    cT
    wceq
    #
    @11
    @12
    @17
    @0
    @5
    @15
    cr
    wcel
    #
    @12
    @17
    cc0
    @14
    cle
    wbr
    #
    @21
    chil
    chil
    cT
    wf
    #
    @22
    cT
    cho
    wcel
    #
    @23
    opsqrlem1.1
    cT
    hmopf
    ax-mp
    #
    cT
    nmopge0
    ax-mp
    #
    @14
    opsqrlem1.2
    sqrtcli
    ax-mp
    #
    @15
    @1
    hmopm
    mpan
    ad2antlr
    @12
    @2
    @18
    @0
    @4
    @21
    @12
    @2
    @18
    @27
    @21
    @12
    wa
    cc0
    @15
    cle
    wbr
    #
    @2
    @18
    @22
    @28
    @26
    @14
    opsqrlem1.2
    sqrtge0i
    ax-mp
    @15
    @1
    leopmuli
    mpanr1
    mpanl1
    ad2ant2lr
    @13
    @4
    @20
    @2
    @13
    @4
    wa
    @19
    @14
    @3
    chot
    co
    #
    cT
    @12
    @19
    @29
    wceq
    @0
    @4
    @12
    @19
    @15
    @1
    @16
    ccom
    #
    chot
    co
    #
    @15
    @15
    @3
    chot
    co
    #
    chot
    co
    #
    @29
    @12
    chil
    chil
    @1
    wf
    #
    chil
    chil
    @16
    wf
    #
    @19
    @31
    wceq
    #
    @1
    hmopf
    #
    @12
    @34
    @35
    @37
    @15
    cc
    wcel
    #
    @34
    @35
    @15
    @27
    recni
    #
    @15
    @1
    homulcl
    mpan
    syl
    @38
    @34
    @35
    @36
    @39
    @15
    @1
    @16
    homco1
    mp3an1
    syl2anc
    @12
    @30
    @32
    @15
    chot
    @12
    @1
    clo
    wcel
    #
    @34
    @30
    @32
    wceq
    #
    @1
    hmoplin
    @37
    @38
    @40
    @34
    @41
    @39
    @15
    @1
    @1
    homco2
    mp3an1
    syl2anc
    oveq2d
    @12
    @29
    @15
    @15
    cmul
    co
    #
    @3
    chot
    co
    #
    @33
    @42
    @14
    @3
    chot
    @22
    @42
    @14
    wceq
    @26
    @14
    opsqrlem1.2
    sqrtthi
    ax-mp
    oveq1i
    @12
    chil
    chil
    @3
    wf
    #
    @43
    @33
    wceq
    #
    @12
    @34
    @34
    @44
    @37
    @37
    chil
    chil
    chil
    @1
    @1
    fco
    syl2anc
    @38
    @38
    @44
    @45
    @39
    @39
    @15
    @15
    @3
    homulass
    mp3an12
    syl
    syl5reqr
    3eqtrd
    ad2antlr
    @0
    @4
    @29
    cT
    wceq
    @12
    @4
    @0
    @29
    @14
    c1
    @14
    cdiv
    co
    #
    cT
    chot
    co
    #
    chot
    co
    #
    cT
    @4
    @3
    @47
    @14
    chot
    @4
    @3
    cR
    @47
    @4
    id
    opsqrlem1.4
    syl6eq
    oveq2d
    @0
    @14
    @46
    cmul
    co
    #
    cT
    chot
    co
    #
    c1
    cT
    chot
    co
    #
    @48
    cT
    @0
    @49
    c1
    cT
    chot
    @0
    @14
    cc0
    wne
    #
    @49
    c1
    wceq
    cT
    clo
    wcel
    #
    @52
    @0
    wb
    @24
    @53
    opsqrlem1.1
    cT
    hmoplin
    ax-mp
    cT
    nmlnopne0
    ax-mp
    #
    @14
    @14
    opsqrlem1.2
    recni
    #
    recidzi
    sylbir
    oveq1d
    @0
    @46
    cc
    wcel
    #
    @50
    @48
    wceq
    #
    @0
    @46
    @0
    @52
    @46
    cr
    wcel
    @54
    @14
    opsqrlem1.2
    rerecclzi
    sylbir
    recnd
    @14
    cc
    wcel
    @56
    @23
    @57
    @55
    @25
    @14
    @46
    cT
    homulass
    mp3an13
    syl
    @23
    @51
    cT
    wceq
    @0
    @25
    cT
    homulid2
    mp1i
    3eqtr3d
    sylan9eqr
    adantlr
    eqtrd
    adantrl
    @10
    @18
    @20
    wa
    vv
    @16
    cho
    @6
    @16
    wceq
    #
    @7
    @18
    @9
    @20
    @6
    @16
    ch0o
    cleo
    breq2
    @58
    @8
    @19
    cT
    @58
    @8
    @16
    @6
    ccom
    @19
    @6
    @16
    @6
    coeq1
    @6
    @16
    @16
    coeq2
    eqtrd
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    opsqrlem1.5
    r19.29a
end
