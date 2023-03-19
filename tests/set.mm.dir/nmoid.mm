include "cngp.mm"
include "wcel.mm"
include "csn.mm"
include "wpss.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cnm.mm"
include "eqid.mm"
include "simpl.mm"
include "cgrp.mm"
include "cghm.mm"
include "co.mm"
include "ngpgrp.mm"
include "adantr.mm"
include "idghm.mm"
include "syl.mm"
include "1red.mm"
include "cc0.mm"
include "0le1.mm"
include "a1i.mm"
include "cv.mm"
include "wne.mm"
include "cmul.mm"
include "cr.mm"
include "nmcl.mm"
include "ad2ant2r.mm"
include "leidd.mm"
include "fvresi.mm"
include "ad2antrl.mm"
include "fveq2d.mm"
include "recnd.mm"
include "mulid2d.mm"
include "3brtr4d.mm"
include "nmolb2d.mm"
include "wn.mm"
include "wex.mm"
include "pssnel.mm"
include "adantl.mm"
include "velsn.mm"
include "biimpri.mm"
include "necon3bi.mm"
include "eqtr4d.mm"
include "cnghm.mm"
include "cxr.mm"
include "nmocl.mm"
include "syl3anc.mm"
include "nmoge0.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "wb.mm"
include "isnghm2.mm"
include "mpbird.mm"
include "simprl.mm"
include "nmoi.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "crp.mm"
include "nmrpcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "lemul1d.mm"
include "sylanr2.mm"
include "exlimddv.mm"
include "1re.mm"
include "rexri.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem nmoid
  let cS: class S
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  assume nmoid.1: |- N = ( S normOp S )
  assume nmoid.2: |- V = ( Base ` S )
  assume nmoid.3: |- .0. = ( 0g ` S )


  assert |- ( ( S e. NrmGrp /\ { .0. } C. V ) -> ( N ` ( _I |` V ) ) = 1 )

  proof
    cS
    cngp
    wcel
    #
    c.0
    csn
    #
    cV
    wpss
    #
    wa
    #
    cid
    cV
    cres
    #
    cN
    cfv
    #
    c1
    wceq
    #
    @5
    c1
    cle
    wbr
    #
    c1
    @5
    cle
    wbr
    #
    @3
    vx
    c1
    cS
    cS
    @4
    cS
    cnm
    cfv
    #
    @9
    cN
    cV
    c.0
    nmoid.1
    nmoid.2
    @9
    eqid
    #
    @10
    nmoid.3
    @0
    @2
    simpl
    #
    @11
    @3
    cS
    cgrp
    wcel
    #
    @4
    cS
    cS
    cghm
    co
    wcel
    #
    @0
    @12
    @2
    cS
    ngpgrp
    adantr
    cV
    cS
    nmoid.2
    idghm
    syl
    #
    @3
    1red
    #
    cc0
    c1
    cle
    wbr
    @3
    0le1
    a1i
    @3
    vx
    cv
    #
    cV
    wcel
    #
    @16
    c.0
    wne
    #
    wa
    #
    wa
    #
    @16
    @9
    cfv
    #
    @21
    @16
    @4
    cfv
    #
    @9
    cfv
    #
    c1
    @21
    cmul
    co
    #
    cle
    @20
    @21
    @0
    @17
    @21
    cr
    wcel
    @2
    @18
    @16
    cS
    @9
    cV
    nmoid.2
    @10
    nmcl
    ad2ant2r
    #
    leidd
    @20
    @22
    @16
    @9
    @17
    @22
    @16
    wceq
    @3
    @18
    cV
    @16
    fvresi
    ad2antrl
    fveq2d
    #
    @20
    @21
    @20
    @21
    @25
    recnd
    mulid2d
    #
    3brtr4d
    nmolb2d
    #
    @3
    @17
    @16
    @1
    wcel
    #
    wn
    #
    wa
    #
    @8
    vx
    @2
    @31
    vx
    wex
    @0
    vx
    @1
    cV
    pssnel
    adantl
    @30
    @3
    @17
    @18
    @8
    @29
    @16
    c.0
    @29
    @16
    c.0
    wceq
    vx
    c.0
    velsn
    biimpri
    necon3bi
    @20
    @8
    @24
    @5
    @21
    cmul
    co
    #
    cle
    wbr
    @20
    @24
    @23
    @32
    cle
    @20
    @24
    @21
    @23
    @27
    @26
    eqtr4d
    @20
    @4
    cS
    cS
    cnghm
    co
    wcel
    #
    @17
    @23
    @32
    cle
    wbr
    @3
    @33
    @19
    @3
    @33
    @5
    cr
    wcel
    #
    @3
    @5
    cxr
    wcel
    #
    c1
    cr
    wcel
    cc0
    @5
    cle
    wbr
    #
    @7
    @34
    @3
    @0
    @0
    @13
    @35
    @11
    @11
    @14
    cS
    cS
    @4
    cN
    nmoid.1
    nmocl
    syl3anc
    #
    @15
    @3
    @0
    @0
    @13
    @36
    @11
    @11
    @14
    cS
    cS
    @4
    cN
    nmoid.1
    nmoge0
    syl3anc
    @28
    @5
    c1
    xrrege0
    syl22anc
    #
    @3
    @0
    @0
    @13
    @33
    @34
    wb
    @11
    @11
    @14
    cS
    cS
    @4
    cN
    nmoid.1
    isnghm2
    syl3anc
    mpbird
    adantr
    @3
    @17
    @18
    simprl
    cS
    cS
    @4
    @9
    @9
    cN
    cV
    @16
    nmoid.1
    nmoid.2
    @10
    @10
    nmoi
    syl2anc
    eqbrtrd
    @20
    c1
    @5
    @21
    @20
    1red
    @3
    @34
    @19
    @38
    adantr
    @0
    @19
    @21
    crp
    wcel
    #
    @2
    @0
    @17
    @18
    @39
    @16
    cS
    @9
    cV
    c.0
    nmoid.2
    @10
    nmoid.3
    nmrpcl
    3expb
    adantlr
    lemul1d
    mpbird
    sylanr2
    exlimddv
    @3
    @35
    c1
    cxr
    wcel
    @6
    @7
    @8
    wa
    wb
    @37
    c1
    1re
    rexri
    @5
    c1
    xrletri3
    sylancl
    mpbir2and
end
