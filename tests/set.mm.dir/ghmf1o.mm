include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wa.mm"
include "cgrp.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "ghmgrp2.mm"
include "ghmgrp1.mm"
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
include "ghmlin.mm"
include "syl3anc.mm"
include "simplr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "wi.mm"
include "grpcl.mm"
include "f1ocnvfv.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "isghm.mm"
include "sylanbrc.mm"
include "wfn.mm"
include "ghmf.mm"
include "ffn.mm"
include "dff1o4.mm"
include "impbida.mm"

theorem ghmf1o
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume ghmf1o.x: |- X = ( Base ` S )
  assume ghmf1o.y: |- Y = ( Base ` T )


  assert |- ( F e. ( S GrpHom T ) -> ( F : X -1-1-onto-> Y <-> `' F e. ( T GrpHom S ) ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    cF
    ccnv
    #
    cT
    cS
    cghm
    co
    wcel
    #
    @0
    @1
    wa
    #
    cT
    cgrp
    wcel
    #
    cS
    cgrp
    wcel
    #
    wa
    #
    cY
    cX
    @2
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
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
    cS
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cY
    wral
    vx
    cY
    wral
    #
    wa
    @3
    @0
    @7
    @1
    @0
    @5
    @6
    cS
    cT
    cF
    ghmgrp2
    cS
    cT
    cF
    ghmgrp1
    #
    jca
    adantr
    @4
    @8
    @18
    @4
    cY
    cX
    @2
    wf1o
    #
    @8
    @1
    @20
    @0
    cX
    cY
    cF
    f1ocnv
    adantl
    cY
    cX
    @2
    f1of
    syl
    #
    @4
    @17
    vx
    vy
    cY
    cY
    @4
    @9
    cY
    wcel
    #
    @10
    cY
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
    @25
    @26
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
    @25
    @0
    @13
    cX
    wcel
    #
    @14
    cX
    wcel
    #
    @26
    @30
    wceq
    @0
    @1
    @24
    simpll
    #
    @25
    cY
    cX
    @9
    @2
    @4
    @8
    @24
    @21
    adantr
    #
    @4
    @22
    @23
    simprl
    #
    ffvelrnd
    #
    @25
    cY
    cX
    @10
    @2
    @34
    @4
    @22
    @23
    simprr
    #
    ffvelrnd
    #
    @15
    @11
    cS
    cT
    @13
    cF
    @14
    cX
    ghmf1o.x
    @15
    eqid
    #
    @11
    eqid
    #
    ghmlin
    syl3anc
    @25
    @28
    @9
    @29
    @10
    @11
    @25
    @1
    @22
    @28
    @9
    wceq
    @0
    @1
    @24
    simplr
    #
    @35
    cX
    cY
    @9
    cF
    f1ocnvfv2
    syl2anc
    @25
    @1
    @23
    @29
    @10
    wceq
    @41
    @37
    cX
    cY
    @10
    cF
    f1ocnvfv2
    syl2anc
    oveq12d
    eqtrd
    @25
    @1
    @16
    cX
    wcel
    #
    @27
    @17
    wi
    @41
    @25
    @6
    @31
    @32
    @42
    @25
    @0
    @6
    @33
    @19
    syl
    @36
    @38
    cX
    @15
    cS
    @13
    @14
    ghmf1o.x
    @39
    grpcl
    syl3anc
    cX
    cY
    @16
    @12
    cF
    f1ocnvfv
    syl2anc
    mpd
    ralrimivva
    jca
    vy
    vx
    @11
    @15
    cT
    cS
    @2
    cY
    cX
    ghmf1o.y
    ghmf1o.x
    @40
    @39
    isghm
    sylanbrc
    @0
    @3
    wa
    #
    cF
    cX
    wfn
    #
    @2
    cY
    wfn
    #
    @1
    @43
    cX
    cY
    cF
    wf
    #
    @44
    @0
    @46
    @3
    cS
    cT
    cF
    cX
    cY
    ghmf1o.x
    ghmf1o.y
    ghmf
    adantr
    cX
    cY
    cF
    ffn
    syl
    @43
    @8
    @45
    @3
    @8
    @0
    cT
    cS
    @2
    cY
    cX
    ghmf1o.y
    ghmf1o.x
    ghmf
    adantl
    cY
    cX
    @2
    ffn
    syl
    cX
    cY
    cF
    dff1o4
    sylanbrc
    impbida
end
