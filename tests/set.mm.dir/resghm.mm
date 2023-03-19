include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cplusg.mm"
include "cres.mm"
include "cbs.mm"
include "eqid.mm"
include "cgrp.mm"
include "subggrp.mm"
include "adantl.mm"
include "ghmgrp2.mm"
include "adantr.mm"
include "wf.mm"
include "wss.mm"
include "ghmf.mm"
include "subgss.mm"
include "fssres.mm"
include "syl2an.mm"
include "wceq.mm"
include "ressbas2.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbid.mm"
include "cv.mm"
include "wb.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "biimpar.mm"
include "simpll.mm"
include "sselda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "ghmlin.mm"
include "syl3anc.mm"
include "ressplusg.mm"
include "ad2antlr.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "subgcl.mm"
include "3expb.mm"
include "adantll.mm"
include "fvres.mm"
include "eqtr3d.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "syldan.mm"
include "isghmd.mm"

theorem resghm
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume resghm.u: |- U = ( S |`s X )


  assert |- ( ( F e. ( S GrpHom T ) /\ X e. ( SubGrp ` S ) ) -> ( F |` X ) e. ( U GrpHom T ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cX
    cS
    csubg
    cfv
    #
    wcel
    #
    wa
    #
    va
    vb
    cU
    cplusg
    cfv
    #
    cT
    cplusg
    cfv
    #
    cU
    cT
    cF
    cX
    cres
    #
    cU
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    @7
    eqid
    @8
    eqid
    #
    @4
    eqid
    @5
    eqid
    #
    @2
    cU
    cgrp
    wcel
    @0
    cX
    cS
    cU
    resghm.u
    subggrp
    adantl
    @0
    cT
    cgrp
    wcel
    @2
    cS
    cT
    cF
    ghmgrp2
    adantr
    @3
    cX
    @8
    @6
    wf
    #
    @7
    @8
    @6
    wf
    @0
    cS
    cbs
    cfv
    #
    @8
    cF
    wf
    cX
    @12
    wss
    #
    @11
    @2
    cS
    cT
    cF
    @12
    @8
    @12
    eqid
    #
    @9
    ghmf
    @12
    cX
    cS
    @14
    subgss
    #
    @12
    @8
    cX
    cF
    fssres
    syl2an
    @3
    cX
    @7
    @8
    @6
    @3
    @13
    cX
    @7
    wceq
    #
    @2
    @13
    @0
    @15
    adantl
    #
    cX
    @12
    cU
    cS
    resghm.u
    @14
    ressbas2
    syl
    #
    feq2d
    mpbid
    @3
    va
    cv
    #
    @7
    wcel
    #
    vb
    cv
    #
    @7
    wcel
    #
    wa
    #
    @19
    cX
    wcel
    #
    @21
    cX
    wcel
    #
    wa
    #
    @19
    @21
    @4
    co
    #
    @6
    cfv
    #
    @19
    @6
    cfv
    #
    @21
    @6
    cfv
    #
    @5
    co
    #
    wceq
    @3
    @26
    @23
    @3
    @16
    @26
    @23
    wb
    @18
    @16
    @24
    @20
    @25
    @22
    cX
    @7
    @19
    eleq2
    cX
    @7
    @21
    eleq2
    anbi12d
    syl
    biimpar
    @3
    @26
    wa
    #
    @19
    @21
    cS
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    @21
    cF
    cfv
    #
    @5
    co
    #
    @28
    @31
    @32
    @0
    @19
    @12
    wcel
    #
    @21
    @12
    wcel
    #
    @35
    @38
    wceq
    @0
    @2
    @26
    simpll
    @3
    @24
    @39
    @25
    @3
    cX
    @12
    @19
    @17
    sselda
    adantrr
    @3
    @25
    @40
    @24
    @3
    cX
    @12
    @21
    @17
    sselda
    adantrl
    @33
    @5
    cS
    cT
    @19
    cF
    @21
    @12
    @14
    @33
    eqid
    #
    @10
    ghmlin
    syl3anc
    @32
    @34
    @6
    cfv
    #
    @28
    @35
    @32
    @34
    @27
    @6
    @32
    @33
    @4
    @19
    @21
    @2
    @33
    @4
    wceq
    @0
    @26
    cX
    @33
    cS
    cU
    @1
    resghm.u
    @41
    ressplusg
    ad2antlr
    oveqd
    fveq2d
    @32
    @34
    cX
    wcel
    #
    @42
    @35
    wceq
    @2
    @26
    @43
    @0
    @2
    @24
    @25
    @43
    @33
    cX
    cS
    @19
    @21
    @41
    subgcl
    3expb
    adantll
    @34
    cX
    cF
    fvres
    syl
    eqtr3d
    @26
    @31
    @38
    wceq
    @3
    @24
    @25
    @29
    @36
    @30
    @37
    @5
    @19
    cX
    cF
    fvres
    @21
    cX
    cF
    fvres
    oveqan12d
    adantl
    3eqtr4d
    syldan
    isghmd
end
