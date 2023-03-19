include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "symgfixf.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "wb.mm"
include "fvtresfn.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "wf1o.mm"
include "cvv.mm"
include "vex.mm"
include "symgfixelq.mm"
include "ax-mp.mm"
include "anbi12i.mm"
include "wfn.mm"
include "wss.mm"
include "f1ofn.mm"
include "adantr.mm"
include "anim12i.mm"
include "difss.mm"
include "jctir.mm"
include "fvreseq.mm"
include "syl.mm"
include "cdm.mm"
include "f1of.mm"
include "fdm.mm"
include "syl2an.mm"
include "eqtr3.mm"
include "ad2antlr.mm"
include "cun.mm"
include "simpr.mm"
include "ad2ant2l.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "ralunsn.mm"
include "mpbir2and.mm"
include "f1odm.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "wfun.mm"
include "f1ofun.mm"
include "eqfunfv.mm"
include "ex.mm"
include "sylbid.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem symgfixf1
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cH: class H
  let cK: class K
  let cN: class N
  let vq: setvar q
  let vg: setvar g
  let vp: setvar p
  let vi: setvar i
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }
  assume symgfixf.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgfixf.h: |- H = ( q e. Q |-> ( q |` ( N \ { K } ) ) )

  disjoint K q
  disjoint P q
  disjoint N q
  disjoint Q q
  disjoint S q
  disjoint H g
  disjoint H p
  disjoint g p
  disjoint K g
  disjoint K i
  disjoint K p
  disjoint g i
  disjoint i p
  disjoint N g
  disjoint N i
  disjoint N p
  disjoint g q
  disjoint i q
  disjoint p q
  disjoint Q g
  disjoint Q p
  assert |- ( K e. N -> H : Q -1-1-> S )

  proof
    cK
    cN
    wcel
    #
    cQ
    cS
    cH
    wf
    vg
    cv
    #
    cH
    cfv
    #
    vp
    cv
    #
    cH
    cfv
    #
    wceq
    #
    vg
    vp
    weq
    #
    wi
    #
    vp
    cQ
    wral
    vg
    cQ
    wral
    cQ
    cS
    cH
    wf1
    cP
    cQ
    cS
    cH
    cK
    cN
    vq
    symgfixf.p
    symgfixf.q
    symgfixf.s
    symgfixf.h
    symgfixf
    @0
    @7
    vg
    vp
    cQ
    cQ
    @0
    @1
    cQ
    wcel
    #
    @3
    cQ
    wcel
    #
    wa
    #
    wa
    @5
    @1
    cN
    cK
    csn
    #
    cdif
    #
    cres
    #
    @3
    @12
    cres
    #
    wceq
    #
    @6
    @10
    @5
    @15
    wb
    @0
    @8
    @9
    @2
    @13
    @4
    @14
    vq
    cQ
    cH
    @12
    @1
    symgfixf.h
    fvtresfn
    vq
    cQ
    cH
    @12
    @3
    symgfixf.h
    fvtresfn
    eqeqan12d
    adantl
    @10
    @0
    cN
    cN
    @1
    wf1o
    #
    cK
    @1
    cfv
    #
    cK
    wceq
    #
    wa
    #
    cN
    cN
    @3
    wf1o
    #
    cK
    @3
    cfv
    #
    cK
    wceq
    #
    wa
    #
    wa
    #
    @15
    @6
    wi
    @8
    @19
    @9
    @23
    @1
    cvv
    wcel
    @8
    @19
    wb
    vg
    vex
    cP
    cQ
    @1
    cK
    cN
    cvv
    vq
    symgfixf.p
    symgfixf.q
    symgfixelq
    ax-mp
    @3
    cvv
    wcel
    @9
    @23
    wb
    vp
    vex
    cP
    cQ
    @3
    cK
    cN
    cvv
    vq
    symgfixf.p
    symgfixf.q
    symgfixelq
    ax-mp
    anbi12i
    @0
    @24
    wa
    #
    @15
    vi
    cv
    #
    @1
    cfv
    #
    @26
    @3
    cfv
    #
    wceq
    #
    vi
    @12
    wral
    #
    @6
    @25
    @1
    cN
    wfn
    #
    @3
    cN
    wfn
    #
    wa
    #
    @12
    cN
    wss
    #
    wa
    #
    @15
    @30
    wb
    @24
    @35
    @0
    @24
    @33
    @34
    @19
    @31
    @23
    @32
    @16
    @31
    @18
    cN
    cN
    @1
    f1ofn
    adantr
    @20
    @32
    @22
    cN
    cN
    @3
    f1ofn
    adantr
    anim12i
    cN
    @11
    difss
    jctir
    adantl
    vi
    cN
    @12
    @1
    @3
    fvreseq
    syl
    @25
    @30
    @6
    @25
    @30
    wa
    #
    @6
    @1
    cdm
    #
    @3
    cdm
    #
    wceq
    #
    @29
    vi
    @37
    wral
    #
    @24
    @39
    @0
    @30
    @24
    @37
    cN
    wceq
    #
    @38
    cN
    wceq
    #
    wa
    #
    @39
    @19
    cN
    cN
    @1
    wf
    #
    cN
    cN
    @3
    wf
    #
    @43
    @23
    @16
    @44
    @18
    cN
    cN
    @1
    f1of
    adantr
    @20
    @45
    @22
    cN
    cN
    @3
    f1of
    adantr
    @44
    @41
    @45
    @42
    cN
    cN
    @1
    fdm
    cN
    cN
    @3
    fdm
    anim12i
    syl2an
    @37
    @38
    cN
    eqtr3
    syl
    ad2antlr
    @36
    @40
    @29
    vi
    @12
    @11
    cun
    #
    wral
    #
    @36
    @47
    @30
    @17
    @21
    wceq
    #
    @25
    @30
    simpr
    @24
    @48
    @0
    @30
    @18
    @22
    @48
    @16
    @20
    @17
    @21
    cK
    eqtr3
    ad2ant2l
    ad2antlr
    @25
    @47
    @30
    @48
    wa
    wb
    #
    @30
    @0
    @49
    @24
    @29
    @48
    vi
    @12
    cK
    cN
    @26
    cK
    wceq
    @27
    @17
    @28
    @21
    @26
    cK
    @1
    fveq2
    @26
    cK
    @3
    fveq2
    eqeq12d
    ralunsn
    adantr
    adantr
    mpbir2and
    @36
    @29
    vi
    @37
    @46
    @25
    @37
    @46
    wceq
    @30
    @24
    @0
    @37
    cN
    @46
    @19
    @41
    @23
    @16
    @41
    @18
    cN
    cN
    @1
    f1odm
    adantr
    adantr
    @0
    @46
    cN
    cN
    cK
    difsnid
    eqcomd
    sylan9eqr
    adantr
    raleqdv
    mpbird
    @36
    @1
    wfun
    #
    @3
    wfun
    #
    wa
    #
    @6
    @39
    @40
    wa
    wb
    @24
    @52
    @0
    @30
    @19
    @50
    @23
    @51
    @16
    @50
    @18
    cN
    cN
    @1
    f1ofun
    adantr
    @20
    @51
    @22
    cN
    cN
    @3
    f1ofun
    adantr
    anim12i
    ad2antlr
    vi
    @1
    @3
    eqfunfv
    syl
    mpbir2and
    ex
    sylbid
    sylan2b
    sylbid
    ralrimivva
    vg
    vp
    cQ
    cS
    cH
    dff13
    sylanbrc
end
