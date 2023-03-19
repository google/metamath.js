include "cufl.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "domeng.mm"
include "wf1o.mm"
include "bren.mm"
include "biimpi.mm"
include "ssufl.mm"
include "wi.mm"
include "cufil.mm"
include "cfv.mm"
include "wrex.mm"
include "cfil.mm"
include "wral.mm"
include "cfm.mm"
include "co.mm"
include "simplr.mm"
include "cfbas.mm"
include "wf.mm"
include "filfbas.mm"
include "adantl.mm"
include "f1of.mm"
include "ad2antrr.mm"
include "fmfil.mm"
include "syl3anc.mm"
include "ufli.mm"
include "syl2anc.mm"
include "ccnv.mm"
include "cvv.mm"
include "cdm.mm"
include "wceq.mm"
include "f1odm.mm"
include "adantr.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "simprl.mm"
include "f1ocnv.mm"
include "ad3antrrr.mm"
include "syl.mm"
include "fmufil.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "f1ococnv1.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "fmco.mm"
include "syl32anc.mm"
include "fmid.mm"
include "3eqtr3d.mm"
include "ufilfil.mm"
include "3syl.mm"
include "simprr.mm"
include "fmss.mm"
include "eqsstr3d.mm"
include "sseq2.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "wb.mm"
include "isufl.mm"
include "mpbird.mm"
include "ex.mm"
include "exlimiv.mm"
include "imp.mm"
include "syl2an.mm"
include "an12s.mm"
include "exlimdv.mm"
include "sylbid.mm"

theorem ufldom
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cZ: class Z


  assert |- ( ( X e. UFL /\ Y ~<_ X ) -> Y e. UFL )

  proof
    cX
    cufl
    wcel
    #
    cY
    cX
    cdom
    wbr
    #
    cY
    cufl
    wcel
    #
    @0
    @1
    cY
    vx
    cv
    #
    cen
    wbr
    #
    @3
    cX
    wss
    #
    wa
    #
    vx
    wex
    @2
    vx
    cY
    cX
    cufl
    domeng
    @0
    @6
    @2
    vx
    @0
    @6
    @2
    @4
    @0
    @5
    @2
    @4
    cY
    @3
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @3
    cufl
    wcel
    #
    @2
    @0
    @5
    wa
    @4
    @9
    cY
    @3
    vf
    bren
    biimpi
    cX
    @3
    ssufl
    @9
    @10
    @2
    @8
    @10
    @2
    wi
    vf
    @8
    @10
    @2
    @8
    @10
    wa
    #
    @2
    vg
    cv
    #
    vu
    cv
    #
    wss
    #
    vu
    cY
    cufil
    cfv
    #
    wrex
    #
    vg
    cY
    cfil
    cfv
    #
    wral
    #
    @11
    @16
    vg
    @17
    @11
    @12
    @17
    wcel
    #
    wa
    #
    @12
    @3
    @7
    cfm
    co
    cfv
    #
    vy
    cv
    #
    wss
    #
    @16
    vy
    @3
    cufil
    cfv
    #
    @20
    @10
    @21
    @3
    cfil
    cfv
    #
    wcel
    #
    @23
    vy
    @24
    wrex
    @8
    @10
    @19
    simplr
    #
    @20
    @10
    @12
    cY
    cfbas
    cfv
    wcel
    #
    cY
    @3
    @7
    wf
    #
    @26
    @27
    @19
    @28
    @11
    @12
    cY
    filfbas
    adantl
    #
    @8
    @29
    @10
    @19
    cY
    @3
    @7
    f1of
    #
    ad2antrr
    cufl
    @12
    @7
    @3
    cY
    fmfil
    syl3anc
    #
    vy
    @21
    @3
    ufli
    syl2anc
    @20
    @22
    @24
    wcel
    #
    @23
    wa
    #
    wa
    #
    @22
    cY
    @7
    ccnv
    #
    cfm
    co
    #
    cfv
    #
    @15
    wcel
    #
    @12
    @38
    wss
    #
    @16
    @35
    cY
    cvv
    wcel
    #
    @33
    @3
    cY
    @36
    wf
    #
    @39
    @11
    @41
    @19
    @34
    @11
    cY
    @7
    cdm
    #
    cvv
    @8
    @43
    cY
    wceq
    @10
    cY
    @3
    @7
    f1odm
    adantr
    @7
    vf
    vex
    dmex
    syl6eqelr
    #
    ad2antrr
    #
    @20
    @33
    @23
    simprl
    #
    @35
    @3
    cY
    @36
    wf1o
    #
    @42
    @8
    @47
    @10
    @19
    @34
    cY
    @3
    @7
    f1ocnv
    ad3antrrr
    @3
    cY
    @36
    f1of
    syl
    #
    cvv
    @36
    @22
    cY
    @3
    fmufil
    syl3anc
    @35
    @12
    @21
    @37
    cfv
    #
    @38
    @35
    @12
    cY
    @36
    @7
    ccom
    #
    cfm
    co
    #
    cfv
    #
    @12
    cY
    cid
    cY
    cres
    #
    cfm
    co
    #
    cfv
    #
    @49
    @12
    @35
    @12
    @51
    @54
    @35
    @50
    @53
    cY
    cfm
    @8
    @50
    @53
    wceq
    @10
    @19
    @34
    cY
    @3
    @7
    f1ococnv1
    ad3antrrr
    oveq2d
    fveq1d
    @35
    @41
    @10
    @28
    @42
    @29
    @52
    @49
    wceq
    @45
    @20
    @10
    @34
    @27
    adantr
    @20
    @28
    @34
    @30
    adantr
    @48
    @8
    @29
    @10
    @19
    @34
    @31
    ad3antrrr
    @12
    @36
    @7
    cvv
    cufl
    cY
    @3
    cY
    fmco
    syl32anc
    @35
    @19
    @55
    @12
    wceq
    @11
    @19
    @34
    simplr
    @12
    cY
    fmid
    syl
    3eqtr3d
    @35
    @41
    @21
    @3
    cfbas
    cfv
    #
    wcel
    #
    @22
    @56
    wcel
    #
    @42
    @23
    @49
    @38
    wss
    @45
    @35
    @26
    @57
    @20
    @26
    @34
    @32
    adantr
    @21
    @3
    filfbas
    syl
    @35
    @33
    @22
    @25
    wcel
    @58
    @46
    @22
    @3
    ufilfil
    @22
    @3
    filfbas
    3syl
    @48
    @20
    @33
    @23
    simprr
    cvv
    @21
    @22
    @36
    cY
    @3
    fmss
    syl32anc
    eqsstr3d
    @14
    @40
    vu
    @38
    @15
    @13
    @38
    @12
    sseq2
    rspcev
    syl2anc
    rexlimddv
    ralrimiva
    @11
    @41
    @2
    @18
    wb
    @44
    vg
    vu
    cvv
    cY
    isufl
    syl
    mpbird
    ex
    exlimiv
    imp
    syl2an
    an12s
    ex
    exlimdv
    sylbid
    imp
end
