include "ccusgr.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "wceq.mm"
include "cedg.mm"
include "edgval.mm"
include "eqtri.mm"
include "a1i.mm"
include "fveq2d.mm"
include "cop.mm"
include "cvtx.mm"
include "opeq1i.mm"
include "cusgrop.mm"
include "syl5eqel.mm"
include "cv.mm"
include "cid.mm"
include "wnel.mm"
include "crab.mm"
include "cres.mm"
include "csn.mm"
include "cdif.mm"
include "fvex.mm"
include "cvv.mm"
include "rabexg.mm"
include "resiexd.mm"
include "ax-mp.mm"
include "rneq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeqan12rd.mm"
include "vex.mm"
include "opvtxfvi.mm"
include "eqcomi.mm"
include "eqid.mm"
include "cusgrres.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "cc0.mm"
include "edgopval.mm"
include "mp2an.mm"
include "eqcomd.mm"
include "cuhgr.mm"
include "cusgr.mm"
include "cusgrusgr.mm"
include "usgruhgr.mm"
include "syl.mm"
include "cusgrsizeindb0.mm"
include "sylan.mm"
include "eqtrd.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "w3a.mm"
include "rnresi.mm"
include "fveq2i.mm"
include "rabeqdv.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "imdistani.mm"
include "cusgrsize2inds.mm"
include "imp31.mm"
include "opfi1ind.mm"

theorem cusgrsize
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let cN: class N
  let vv: setvar v
  let vc: setvar c
  let vw: setvar w
  let vy: setvar y
  assume cusgrsizeindb0.v: |- V = ( Vtx ` G )
  assume cusgrsizeindb0.e: |- E = ( Edg ` G )


  assert |- ( ( G e. ComplUSGraph /\ V e. Fin ) -> ( # ` E ) = ( ( # ` V ) _C 2 ) )

  proof
    cG
    ccusgr
    wcel
    #
    cV
    cfn
    wcel
    #
    wa
    #
    cE
    chash
    cfv
    cG
    ciedg
    cfv
    #
    crn
    #
    chash
    cfv
    #
    cV
    chash
    cfv
    #
    c2
    cbc
    co
    #
    @2
    cE
    @4
    chash
    cE
    @4
    wceq
    @2
    cE
    cG
    cedg
    cfv
    @4
    cusgrsizeindb0.e
    cG
    edgval
    eqtri
    a1i
    fveq2d
    @0
    cV
    @3
    cop
    #
    ccusgr
    wcel
    @1
    @5
    @7
    wceq
    #
    @0
    @8
    cG
    cvtx
    cfv
    #
    @3
    cop
    ccusgr
    cV
    @10
    @3
    cusgrsizeindb0.v
    opeq1i
    cG
    cusgrop
    syl5eqel
    @9
    ve
    cv
    #
    crn
    #
    chash
    cfv
    #
    vv
    cv
    #
    chash
    cfv
    #
    c2
    cbc
    co
    #
    wceq
    #
    cid
    vn
    cv
    #
    vc
    cv
    wnel
    #
    vc
    @14
    @11
    cop
    #
    cedg
    cfv
    #
    crab
    #
    cres
    #
    crn
    #
    chash
    cfv
    #
    @14
    @18
    csn
    cdif
    #
    chash
    cfv
    #
    c2
    cbc
    co
    #
    wceq
    #
    vf
    cv
    #
    crn
    #
    chash
    cfv
    #
    vw
    cv
    #
    chash
    cfv
    #
    c2
    cbc
    co
    #
    wceq
    vy
    vw
    vv
    ve
    vf
    vn
    @3
    @23
    ccusgr
    cV
    cG
    ciedg
    fvex
    @21
    cvv
    wcel
    #
    @23
    cvv
    wcel
    @20
    cedg
    fvex
    @36
    @22
    cvv
    @19
    vc
    @21
    cvv
    rabexg
    resiexd
    ax-mp
    @11
    @3
    wceq
    #
    @14
    cV
    wceq
    #
    @13
    @5
    @16
    @7
    @37
    @12
    @4
    chash
    @11
    @3
    rneq
    fveq2d
    @38
    @15
    @6
    c2
    cbc
    @14
    cV
    chash
    fveq2
    oveq1d
    eqeqan12rd
    @11
    @30
    wceq
    #
    @14
    @33
    wceq
    #
    @13
    @32
    @16
    @35
    @39
    @12
    @31
    chash
    @11
    @30
    rneq
    fveq2d
    @40
    @15
    @34
    c2
    cbc
    @14
    @33
    chash
    fveq2
    oveq1d
    eqeqan12rd
    @26
    @23
    cop
    #
    vc
    @21
    @22
    @20
    @18
    @14
    @20
    cvtx
    cfv
    @14
    @11
    @14
    vv
    vex
    #
    ve
    vex
    #
    opvtxfvi
    eqcomi
    #
    @21
    eqid
    #
    @22
    eqid
    @41
    eqid
    cusgrres
    @33
    @26
    wceq
    #
    @30
    @23
    wceq
    #
    wa
    #
    @32
    @25
    @35
    @28
    @47
    @32
    @25
    wceq
    @46
    @47
    @31
    @24
    chash
    @30
    @23
    rneq
    fveq2d
    adantl
    @48
    @34
    @27
    c2
    cbc
    @46
    @34
    @27
    wceq
    @47
    @33
    @26
    chash
    fveq2
    adantr
    oveq1d
    eqeq12d
    @20
    ccusgr
    wcel
    #
    @15
    cc0
    wceq
    #
    wa
    #
    @13
    @21
    chash
    cfv
    #
    @16
    @51
    @12
    @21
    chash
    @51
    @21
    @12
    @21
    @12
    wceq
    #
    @51
    @14
    cvv
    wcel
    @11
    cvv
    wcel
    @53
    @42
    @43
    @11
    @14
    cvv
    cvv
    edgopval
    mp2an
    #
    a1i
    eqcomd
    fveq2d
    @49
    @20
    cuhgr
    wcel
    #
    @50
    @52
    @16
    wceq
    @49
    @20
    cusgr
    wcel
    @55
    @20
    cusgrusgr
    @20
    usgruhgr
    syl
    @21
    @20
    @14
    @44
    @45
    cusgrsizeindb0
    sylan
    eqtrd
    vy
    cv
    c1
    caddc
    co
    #
    cn0
    wcel
    #
    @49
    @15
    @56
    wceq
    @18
    @14
    wcel
    w3a
    #
    wa
    #
    @29
    wa
    @59
    @19
    vc
    @12
    crab
    #
    chash
    cfv
    #
    @28
    wceq
    #
    wa
    @17
    @59
    @29
    @62
    @59
    @29
    @62
    @59
    @25
    @61
    @28
    @59
    @25
    @22
    chash
    cfv
    @61
    @24
    @22
    chash
    @22
    rnresi
    fveq2i
    @59
    @22
    @60
    chash
    @59
    @19
    vc
    @21
    @12
    @53
    @59
    @54
    a1i
    rabeqdv
    fveq2d
    syl5eq
    eqeq1d
    biimpd
    imdistani
    @57
    @58
    @62
    @17
    vc
    @12
    @60
    @20
    @18
    @14
    @56
    @44
    @21
    @12
    @54
    eqcomi
    @60
    eqid
    cusgrsize2inds
    imp31
    syl
    opfi1ind
    sylan
    eqtrd
end
