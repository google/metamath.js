include "cts.mm"
include "cfv.mm"
include "ctopn.mm"
include "ccom.mm"
include "cpt.mm"
include "cbs.mm"
include "cpw.mm"
include "wss.mm"
include "wceq.mm"
include "cdm.mm"
include "cvv.mm"
include "wfn.mm"
include "wcel.mm"
include "fnex.mm"
include "syl2anc.mm"
include "eqid.mm"
include "eqidd.mm"
include "prdstset.mm"
include "cuni.mm"
include "cv.mm"
include "wral.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "ctg.mm"
include "wf.mm"
include "topnfn.mm"
include "dffn2.mm"
include "sylib.mm"
include "fnfco.mm"
include "sylancr.mm"
include "ptval.mm"
include "unieqd.mm"
include "simpl2.mm"
include "fvco2.mm"
include "sylan.mm"
include "crest.mm"
include "co.mm"
include "topnval.mm"
include "restsspw.mm"
include "eqsstr3i.mm"
include "syl6eqss.mm"
include "sseld.mm"
include "fvex.mm"
include "elpw.mm"
include "syl6ib.mm"
include "ralimdva.mm"
include "imp.mm"
include "sylan2.mm"
include "ss2ixp.mm"
include "syl.mm"
include "simprr.mm"
include "prdsbas2.mm"
include "adantr.mm"
include "3sstr4d.mm"
include "ex.mm"
include "exlimdv.mm"
include "selpw.mm"
include "syl6ibr.mm"
include "abssdv.mm"
include "pwex.mm"
include "ssex.mm"
include "unitg.mm"
include "3syl.mm"
include "eqtrd.mm"
include "sspwuni.mm"
include "eqsstrd.mm"
include "sylibr.mm"
include "topnid.mm"
include "syl6eqr.mm"
include "eqtr3d.mm"

theorem prdstopn
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume prdstopn.y: |- Y = ( S Xs_ R )
  assume prdstopn.s: |- ( ph -> S e. V )
  assume prdstopn.i: |- ( ph -> I e. W )
  assume prdstopn.r: |- ( ph -> R Fn I )
  assume prdstopn.o: |- O = ( TopOpen ` Y )


  assert |- ( ph -> O = ( Xt_ ` ( TopOpen o. R ) ) )

  proof
    wph
    cY
    cts
    cfv
    #
    cO
    ctopn
    cR
    ccom
    #
    cpt
    cfv
    #
    wph
    @0
    cY
    ctopn
    cfv
    #
    cO
    wph
    @0
    cY
    cbs
    cfv
    #
    cpw
    #
    wss
    @0
    @3
    wceq
    wph
    @0
    @2
    @5
    wph
    @4
    cY
    cR
    cS
    cR
    cdm
    #
    @0
    cV
    cvv
    prdstopn.y
    prdstopn.s
    wph
    cR
    cI
    wfn
    #
    cI
    cW
    wcel
    #
    cR
    cvv
    wcel
    prdstopn.r
    prdstopn.i
    cI
    cW
    cR
    fnex
    syl2anc
    @4
    eqid
    #
    wph
    @6
    eqidd
    @0
    eqid
    #
    prdstset
    #
    wph
    @2
    cuni
    #
    @4
    wss
    @2
    @5
    wss
    wph
    @12
    vg
    cv
    #
    cI
    wfn
    #
    vy
    cv
    #
    @13
    cfv
    #
    @15
    @1
    cfv
    #
    wcel
    #
    vy
    cI
    wral
    #
    @16
    @17
    cuni
    wceq
    vy
    cI
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    #
    w3a
    #
    vx
    cv
    #
    vy
    cI
    @16
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    vx
    cab
    #
    cuni
    #
    @4
    wph
    @12
    @27
    ctg
    cfv
    #
    cuni
    #
    @28
    wph
    @2
    @29
    wph
    @8
    @1
    cI
    wfn
    #
    @2
    @29
    wceq
    prdstopn.i
    wph
    ctopn
    cvv
    wfn
    cI
    cvv
    cR
    wf
    #
    @31
    topnfn
    wph
    @7
    @32
    prdstopn.r
    cI
    cR
    dffn2
    sylib
    cvv
    cI
    ctopn
    cR
    fnfco
    sylancr
    vx
    vy
    vz
    cI
    @27
    vg
    @1
    cW
    @27
    eqid
    ptval
    syl2anc
    unieqd
    wph
    @27
    @5
    wss
    #
    @27
    cvv
    wcel
    @30
    @28
    wceq
    wph
    @26
    vx
    @5
    wph
    @26
    @22
    @4
    wss
    #
    @22
    @5
    wcel
    wph
    @25
    @34
    vg
    wph
    @25
    @34
    wph
    @25
    wa
    #
    @23
    vy
    cI
    @15
    cR
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    @22
    @4
    @35
    @16
    @37
    wss
    #
    vy
    cI
    wral
    #
    @23
    @38
    wss
    @25
    wph
    @19
    @40
    @14
    @19
    @20
    @24
    simpl2
    wph
    @19
    @40
    wph
    @18
    @39
    vy
    cI
    wph
    @15
    cI
    wcel
    #
    wa
    #
    @18
    @16
    @37
    cpw
    #
    wcel
    @39
    @42
    @17
    @43
    @16
    @42
    @17
    @36
    ctopn
    cfv
    #
    @43
    wph
    @7
    @41
    @17
    @44
    wceq
    prdstopn.r
    cI
    ctopn
    cR
    @15
    fvco2
    sylan
    @44
    @36
    cts
    cfv
    #
    @37
    crest
    co
    @43
    @37
    @45
    @36
    @37
    eqid
    @45
    eqid
    topnval
    @37
    @45
    restsspw
    eqsstr3i
    syl6eqss
    sseld
    @16
    @37
    @15
    @13
    fvex
    elpw
    syl6ib
    ralimdva
    imp
    sylan2
    vy
    cI
    @16
    @37
    ss2ixp
    syl
    wph
    @21
    @24
    simprr
    wph
    @4
    @38
    wceq
    @25
    wph
    vy
    @4
    cR
    cS
    cI
    cV
    cW
    cY
    prdstopn.y
    @9
    prdstopn.s
    prdstopn.i
    prdstopn.r
    prdsbas2
    adantr
    3sstr4d
    ex
    exlimdv
    vx
    @4
    selpw
    syl6ibr
    abssdv
    #
    @27
    @5
    @4
    cY
    cbs
    fvex
    pwex
    ssex
    @27
    cvv
    unitg
    3syl
    eqtrd
    wph
    @33
    @28
    @4
    wss
    @46
    @27
    @4
    sspwuni
    sylib
    eqsstrd
    @2
    @4
    sspwuni
    sylibr
    eqsstrd
    @4
    @0
    cY
    @9
    @10
    topnid
    syl
    prdstopn.o
    syl6eqr
    @11
    eqtr3d
end
