include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wa.mm"
include "cmnd.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "mhmrcl2.mm"
include "mhmrcl1.mm"
include "jca.mm"
include "adantr.mm"
include "f1ocnv.mm"
include "adantl.mm"
include "f1of.mm"
include "syl.mm"
include "simpll.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "eqid.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "simpr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "wi.mm"
include "mndcl.mm"
include "f1ocnvfv.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "mhm0.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "mndidcl.mm"
include "f1ocnvfv1.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"
include "wfn.mm"
include "mhmf.mm"
include "ffn.mm"
include "dff1o4.mm"
include "impbida.mm"

theorem mhmf1o
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume mhmf1o.b: |- B = ( Base ` R )
  assume mhmf1o.c: |- C = ( Base ` S )


  assert |- ( F e. ( R MndHom S ) -> ( F : B -1-1-onto-> C <-> `' F e. ( S MndHom R ) ) )

  proof
    cF
    cR
    cS
    cmhm
    co
    wcel
    #
    cB
    cC
    cF
    wf1o
    #
    cF
    ccnv
    #
    cS
    cR
    cmhm
    co
    wcel
    #
    @0
    @1
    wa
    #
    cS
    cmnd
    wcel
    #
    cR
    cmnd
    wcel
    #
    wa
    #
    cC
    cB
    @2
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    @2
    cfv
    @9
    @2
    cfv
    #
    @10
    @2
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cC
    wral
    vx
    cC
    wral
    #
    cS
    c0g
    cfv
    #
    @2
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    w3a
    @3
    @0
    @7
    @1
    @0
    @5
    @6
    cR
    cS
    cF
    mhmrcl2
    cR
    cS
    cF
    mhmrcl1
    #
    jca
    adantr
    @4
    @8
    @18
    @22
    @4
    cC
    cB
    @2
    wf1o
    #
    @8
    @1
    @24
    @0
    cB
    cC
    cF
    f1ocnv
    adantl
    cC
    cB
    @2
    f1of
    syl
    #
    @4
    @17
    vx
    vy
    cC
    cC
    @4
    @9
    cC
    wcel
    #
    @10
    cC
    wcel
    #
    wa
    #
    wa
    #
    @16
    cF
    cfv
    #
    @12
    wceq
    #
    @17
    @29
    @30
    @13
    cF
    cfv
    #
    @14
    cF
    cfv
    #
    @11
    co
    #
    @12
    @29
    @0
    @13
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    @30
    @34
    wceq
    @0
    @1
    @28
    simpll
    @29
    cC
    cB
    @9
    @2
    @4
    @8
    @28
    @25
    adantr
    #
    @4
    @26
    @27
    simprl
    #
    ffvelrnd
    #
    @29
    cC
    cB
    @10
    @2
    @37
    @4
    @26
    @27
    simprr
    #
    ffvelrnd
    #
    cB
    @15
    @11
    cR
    cS
    cF
    @13
    @14
    mhmf1o.b
    @15
    eqid
    #
    @11
    eqid
    #
    mhmlin
    syl3anc
    @29
    @32
    @9
    @33
    @10
    @11
    @29
    @1
    @26
    @32
    @9
    wceq
    @4
    @1
    @28
    @0
    @1
    simpr
    #
    adantr
    #
    @38
    cB
    cC
    @9
    cF
    f1ocnvfv2
    syl2anc
    @29
    @1
    @27
    @33
    @10
    wceq
    @45
    @40
    cB
    cC
    @10
    cF
    f1ocnvfv2
    syl2anc
    oveq12d
    eqtrd
    @29
    @1
    @16
    cB
    wcel
    #
    @31
    @17
    wi
    @45
    @29
    @6
    @35
    @36
    @46
    @4
    @6
    @28
    @0
    @6
    @1
    @23
    adantr
    adantr
    @39
    @41
    cB
    @15
    cR
    @13
    @14
    mhmf1o.b
    @42
    mndcl
    syl3anc
    cB
    cC
    @16
    @12
    cF
    f1ocnvfv
    syl2anc
    mpd
    ralrimivva
    @4
    @20
    @21
    cF
    cfv
    #
    @2
    cfv
    #
    @21
    @4
    @19
    @47
    @2
    @4
    @47
    @19
    @0
    @47
    @19
    wceq
    @1
    cR
    cS
    cF
    @19
    @21
    @21
    eqid
    #
    @19
    eqid
    #
    mhm0
    adantr
    eqcomd
    fveq2d
    @4
    @1
    @21
    cB
    wcel
    #
    @48
    @21
    wceq
    @44
    @0
    @51
    @1
    @0
    @6
    @51
    @23
    cB
    cR
    @21
    mhmf1o.b
    @49
    mndidcl
    syl
    adantr
    cB
    cC
    @21
    cF
    f1ocnvfv1
    syl2anc
    eqtrd
    3jca
    vx
    vy
    cC
    cB
    @11
    @15
    cS
    cR
    @2
    @21
    @19
    mhmf1o.c
    mhmf1o.b
    @43
    @42
    @50
    @49
    ismhm
    sylanbrc
    @0
    @3
    wa
    #
    cF
    cB
    wfn
    #
    @2
    cC
    wfn
    #
    @1
    @52
    cB
    cC
    cF
    wf
    #
    @53
    @0
    @55
    @3
    cB
    cC
    cR
    cS
    cF
    mhmf1o.b
    mhmf1o.c
    mhmf
    adantr
    cB
    cC
    cF
    ffn
    syl
    @52
    @8
    @54
    @3
    @8
    @0
    cC
    cB
    cS
    cR
    @2
    mhmf1o.c
    mhmf1o.b
    mhmf
    adantl
    cC
    cB
    @2
    ffn
    syl
    cB
    cC
    cF
    dff1o4
    sylanbrc
    impbida
end
