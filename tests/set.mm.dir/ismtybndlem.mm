include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cismty.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cbl.mm"
include "wceq.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "cbnd.mm"
include "wi.mm"
include "w3a.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wf.mm"
include "isismty.mm"
include "biimp3a.mm"
include "simpld.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnda.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "cima.mm"
include "imaeq2.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "adantr.mm"
include "cxr.mm"
include "rpxr.mm"
include "adantl.mm"
include "anim12dan.mm"
include "ismtyima.mm"
include "syldan.mm"
include "simpl.mm"
include "f1ocnvfv2.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "anassrs.mm"
include "reximdva.mm"
include "syld.mm"
include "ralrimdva.mm"
include "simp2.mm"
include "jctild.mm"
include "3expib.mm"
include "com12.mm"
include "impd.mm"
include "isbndx.mm"
include "3imtr4g.mm"

theorem ismtybndlem
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( N e. ( *Met ` Y ) /\ F e. ( M Ismty N ) ) -> ( M e. ( Bnd ` X ) -> N e. ( Bnd ` Y ) ) )

  proof
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
    wa
    #
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cX
    vx
    cv
    #
    vr
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vx
    cX
    wral
    #
    wa
    @0
    cY
    vy
    cv
    #
    @5
    cN
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vy
    cY
    wral
    #
    wa
    #
    cM
    cX
    cbnd
    cfv
    wcel
    cN
    cY
    cbnd
    cfv
    wcel
    @2
    @3
    @10
    @17
    @3
    @2
    @10
    @17
    wi
    #
    @3
    @0
    @1
    @18
    @3
    @0
    @1
    w3a
    #
    @10
    @16
    @0
    @19
    @10
    @15
    vy
    cY
    @19
    @11
    cY
    wcel
    #
    wa
    #
    @10
    cX
    @11
    cF
    ccnv
    #
    cfv
    #
    @5
    @6
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    @15
    @21
    @23
    cX
    wcel
    #
    @10
    @26
    wi
    @19
    cY
    cX
    @11
    @22
    @19
    cX
    cY
    cF
    wf1o
    #
    cY
    cX
    @22
    wf1o
    cY
    cX
    @22
    wf
    @19
    @28
    vz
    cv
    #
    vw
    cv
    #
    cM
    co
    @29
    cF
    cfv
    @30
    cF
    cfv
    cN
    co
    wceq
    vw
    cX
    wral
    vz
    cX
    wral
    #
    @3
    @0
    @1
    @28
    @31
    wa
    vz
    vw
    cF
    cM
    cN
    cX
    cY
    isismty
    biimp3a
    simpld
    #
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @22
    f1of
    3syl
    ffvelrnda
    #
    @9
    @26
    vx
    @23
    cX
    @4
    @23
    wceq
    #
    @8
    @25
    vr
    crp
    @34
    @7
    @24
    cX
    @4
    @23
    @5
    @6
    oveq1
    eqeq2d
    rexbidv
    rspcv
    syl
    @21
    @25
    @14
    vr
    crp
    @19
    @20
    @5
    crp
    wcel
    #
    @25
    @14
    wi
    @25
    cF
    cX
    cima
    #
    cF
    @24
    cima
    #
    wceq
    @19
    @20
    @35
    wa
    #
    wa
    #
    @14
    cX
    @24
    cF
    imaeq2
    @39
    @36
    cY
    @37
    @13
    @19
    @36
    cY
    wceq
    #
    @38
    @19
    @28
    cX
    cY
    cF
    wfo
    @40
    @32
    cX
    cY
    cF
    f1ofo
    cX
    cY
    cF
    foima
    3syl
    adantr
    @39
    @37
    @23
    cF
    cfv
    #
    @5
    @12
    co
    #
    @13
    @19
    @38
    @27
    @5
    cxr
    wcel
    #
    wa
    @37
    @42
    wceq
    @19
    @20
    @27
    @35
    @43
    @33
    @35
    @43
    @19
    @5
    rpxr
    adantl
    anim12dan
    @23
    @5
    cF
    cM
    cN
    cX
    cY
    ismtyima
    syldan
    @39
    @41
    @11
    @5
    @12
    @19
    @28
    @20
    @41
    @11
    wceq
    @38
    @32
    @20
    @35
    simpl
    cX
    cY
    @11
    cF
    f1ocnvfv2
    syl2an
    oveq1d
    eqtrd
    eqeq12d
    syl5ib
    anassrs
    reximdva
    syld
    ralrimdva
    @3
    @0
    @1
    simp2
    jctild
    3expib
    com12
    impd
    vx
    cM
    cX
    vr
    isbndx
    vy
    cN
    cY
    vr
    isbndx
    3imtr4g
end
