include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cismty.mm"
include "co.mm"
include "w3a.mm"
include "cxr.mm"
include "wa.mm"
include "cbl.mm"
include "cima.mm"
include "cv.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "wss.mm"
include "wf1o.mm"
include "wceq.mm"
include "wral.mm"
include "isismty.mm"
include "biimp3a.mm"
include "adantr.mm"
include "simpld.mm"
include "f1of.mm"
include "syl.mm"
include "frn.mm"
include "syl5ss.mm"
include "sseld.mm"
include "simpl2.mm"
include "simprl.mm"
include "ffvelrn.mm"
include "syl2anc.mm"
include "simprr.mm"
include "blssm.mm"
include "syl3anc.mm"
include "wb.mm"
include "ccnv.mm"
include "clt.mm"
include "wbr.mm"
include "simpl1.mm"
include "simplrr.mm"
include "simplrl.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "sylan.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "wi.mm"
include "simprd.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "impancom.mm"
include "imp.mm"
include "syldan.mm"
include "breq1d.mm"
include "bitrd.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1elima.mm"
include "f1ocnvfv2.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "3bitr4d.mm"
include "eleq1d.mm"
include "3bitr3d.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem ismtyima
  let cP: class P
  let cR: class R
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) /\ F e. ( M Ismty N ) ) /\ ( P e. X /\ R e. RR* ) ) -> ( F " ( P ( ball ` M ) R ) ) = ( ( F ` P ) ( ball ` N ) R ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    cF
    cM
    cN
    cismty
    co
    wcel
    #
    w3a
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    wa
    #
    wa
    #
    vx
    cF
    cP
    cR
    cM
    cbl
    cfv
    co
    #
    cima
    #
    cP
    cF
    cfv
    #
    cR
    cN
    cbl
    cfv
    co
    #
    @7
    vx
    cv
    #
    cY
    wcel
    #
    @12
    @9
    wcel
    #
    @12
    @11
    wcel
    #
    @7
    @9
    cY
    @12
    @7
    @9
    cF
    crn
    #
    cY
    cF
    @8
    imassrn
    @7
    cX
    cY
    cF
    wf
    #
    @16
    cY
    wss
    @7
    cX
    cY
    cF
    wf1o
    #
    @17
    @7
    @18
    @12
    vy
    cv
    #
    cM
    co
    #
    @12
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    cN
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @3
    @18
    @25
    wa
    #
    @6
    @0
    @1
    @2
    @26
    vx
    vy
    cF
    cM
    cN
    cX
    cY
    isismty
    biimp3a
    adantr
    #
    simpld
    #
    cX
    cY
    cF
    f1of
    syl
    #
    cX
    cY
    cF
    frn
    syl
    syl5ss
    sseld
    @7
    @11
    cY
    @12
    @7
    @1
    @10
    cY
    wcel
    #
    @5
    @11
    cY
    wss
    @0
    @1
    @2
    @6
    simpl2
    #
    @7
    @17
    @4
    @30
    @29
    @3
    @4
    @5
    simprl
    #
    cX
    cY
    cP
    cF
    ffvelrn
    syl2anc
    #
    @3
    @4
    @5
    simprr
    #
    cN
    @10
    cR
    cY
    blssm
    syl3anc
    sseld
    @7
    @13
    @14
    @15
    wb
    @7
    @13
    wa
    #
    @12
    cF
    ccnv
    #
    cfv
    #
    cF
    cfv
    #
    @9
    wcel
    #
    @38
    @11
    wcel
    #
    @14
    @15
    @35
    @37
    @8
    wcel
    #
    @10
    @38
    cN
    co
    #
    cR
    clt
    wbr
    #
    @39
    @40
    @35
    @41
    cP
    @37
    cM
    co
    #
    cR
    clt
    wbr
    #
    @43
    @35
    @0
    @5
    @4
    @37
    cX
    wcel
    #
    @41
    @45
    wb
    @7
    @0
    @13
    @0
    @1
    @2
    @6
    simpl1
    #
    adantr
    @3
    @4
    @5
    @13
    simplrr
    #
    @3
    @4
    @5
    @13
    simplrl
    @7
    cY
    cX
    @36
    wf
    #
    @13
    @46
    @7
    @18
    cY
    cX
    @36
    wf1o
    @49
    @28
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @36
    f1of
    3syl
    cY
    cX
    @12
    @36
    ffvelrn
    sylan
    #
    @37
    cM
    cP
    cR
    cX
    elbl2
    syl22anc
    @35
    @44
    @42
    cR
    clt
    @7
    @13
    @46
    @44
    @42
    wceq
    #
    @50
    @7
    @46
    @51
    @7
    @4
    @25
    @46
    @51
    wi
    @32
    @7
    @18
    @25
    @27
    simprd
    @4
    @46
    @25
    @51
    @24
    @51
    cP
    @19
    cM
    co
    #
    @10
    @22
    cN
    co
    #
    wceq
    vx
    vy
    cP
    @37
    cX
    cX
    @12
    cP
    wceq
    #
    @20
    @52
    @23
    @53
    @12
    cP
    @19
    cM
    oveq1
    @54
    @21
    @10
    @22
    cN
    @12
    cP
    cF
    fveq2
    oveq1d
    eqeq12d
    @19
    @37
    wceq
    #
    @52
    @44
    @53
    @42
    @19
    @37
    cP
    cM
    oveq2
    @55
    @22
    @38
    @10
    cN
    @19
    @37
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    impancom
    syl2anc
    imp
    syldan
    breq1d
    bitrd
    @35
    cX
    cY
    cF
    wf1
    #
    @46
    @8
    cX
    wss
    #
    @39
    @41
    wb
    @7
    @56
    @13
    @7
    @18
    @56
    @28
    cX
    cY
    cF
    f1of1
    syl
    adantr
    @50
    @7
    @57
    @13
    @7
    @0
    @4
    @5
    @57
    @47
    @32
    @34
    cM
    cP
    cR
    cX
    blssm
    syl3anc
    adantr
    cX
    cY
    cF
    @37
    @8
    f1elima
    syl3anc
    @35
    @1
    @5
    @30
    @38
    cY
    wcel
    @40
    @43
    wb
    @7
    @1
    @13
    @31
    adantr
    @48
    @7
    @30
    @13
    @33
    adantr
    @35
    @38
    @12
    cY
    @7
    @18
    @13
    @38
    @12
    wceq
    @28
    cX
    cY
    @12
    cF
    f1ocnvfv2
    sylan
    #
    @7
    @13
    simpr
    eqeltrd
    @38
    cN
    @10
    cR
    cY
    elbl2
    syl22anc
    3bitr4d
    @35
    @38
    @12
    @9
    @58
    eleq1d
    @35
    @38
    @12
    @11
    @58
    eleq1d
    3bitr3d
    ex
    pm5.21ndd
    eqrdv
end
