include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "c0g.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "wceq.mm"
include "cplusg.mm"
include "cv.mm"
include "cminusg.mm"
include "cbs.mm"
include "cqus.mm"
include "a1i.mm"
include "eqidd.mm"
include "csubg.mm"
include "wer.mm"
include "nsgsubg.mm"
include "eqid.mm"
include "eqger.mm"
include "syl.mm"
include "subgrcl.mm"
include "eqgcpbl.mm"
include "grpcl.mm"
include "syl3an1.mm"
include "w3a.mm"
include "wa.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "erref.mm"
include "grpass.mm"
include "sylan.mm"
include "breqtrd.mm"
include "grpidcl.mm"
include "grplid.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "grpinvcl.mm"
include "grplinv.mm"
include "qusgrp2.mm"
include "simpld.mm"

theorem qusgrp
  let cS: class S
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let c.pb: class .+b
  let c.pl: class .+
  let cV: class V
  let cX: class X
  let cY: class Y
  assume qusgrp.h: |- H = ( G /s ( G ~QG S ) )


  assert |- ( S e. ( NrmSGrp ` G ) -> H e. Grp )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cH
    cgrp
    wcel
    cG
    c0g
    cfv
    #
    cG
    cS
    cqg
    co
    #
    cec
    cH
    c0g
    cfv
    wceq
    @0
    vu
    vv
    vw
    cG
    cplusg
    cfv
    #
    @2
    cG
    cH
    vu
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cbs
    cfv
    #
    cgrp
    @1
    vd
    vc
    va
    vb
    cH
    cG
    @2
    cqus
    co
    wceq
    @0
    qusgrp.h
    a1i
    @0
    @7
    eqidd
    @0
    @3
    eqidd
    @0
    cS
    cG
    csubg
    cfv
    wcel
    #
    @7
    @2
    wer
    #
    cS
    cG
    nsgsubg
    #
    @2
    cG
    @7
    cS
    @7
    eqid
    #
    @2
    eqid
    #
    eqger
    syl
    #
    @0
    @8
    cG
    cgrp
    wcel
    #
    @10
    cS
    cG
    subgrcl
    syl
    #
    va
    cv
    vb
    cv
    vc
    cv
    vd
    cv
    @3
    @2
    cG
    @7
    cS
    @11
    @12
    @3
    eqid
    #
    eqgcpbl
    @0
    @14
    @4
    @7
    wcel
    #
    vv
    cv
    #
    @7
    wcel
    #
    @4
    @18
    @3
    co
    #
    @7
    wcel
    #
    @15
    @7
    @3
    cG
    @4
    @18
    @11
    @16
    grpcl
    #
    syl3an1
    @0
    @17
    @19
    vw
    cv
    #
    @7
    wcel
    #
    w3a
    #
    wa
    #
    @20
    @23
    @3
    co
    #
    @27
    @4
    @18
    @23
    @3
    co
    @3
    co
    #
    @2
    @26
    @27
    @2
    @7
    @0
    @9
    @25
    @13
    adantr
    @26
    @14
    @21
    @24
    @27
    @7
    wcel
    @0
    @14
    @25
    @15
    adantr
    #
    @26
    @14
    @17
    @19
    @21
    @29
    @0
    @17
    @19
    @24
    simpr1
    @0
    @17
    @19
    @24
    simpr2
    @22
    syl3anc
    @0
    @17
    @19
    @24
    simpr3
    @7
    @3
    cG
    @20
    @23
    @11
    @16
    grpcl
    syl3anc
    erref
    @0
    @14
    @25
    @27
    @28
    wceq
    @15
    @7
    @3
    cG
    @4
    @18
    @23
    @11
    @16
    grpass
    sylan
    breqtrd
    @0
    @14
    @1
    @7
    wcel
    #
    @15
    @7
    cG
    @1
    @11
    @1
    eqid
    #
    grpidcl
    syl
    #
    @0
    @17
    wa
    #
    @1
    @4
    @3
    co
    #
    @4
    @4
    @2
    @0
    @14
    @17
    @34
    @4
    wceq
    @15
    @7
    @3
    cG
    @4
    @1
    @11
    @16
    @31
    grplid
    sylan
    @33
    @4
    @2
    @7
    @0
    @9
    @17
    @13
    adantr
    #
    @0
    @17
    simpr
    erref
    eqbrtrd
    @0
    @14
    @17
    @6
    @7
    wcel
    @15
    @7
    cG
    @5
    @4
    @11
    @5
    eqid
    #
    grpinvcl
    sylan
    @33
    @6
    @4
    @3
    co
    #
    @1
    @1
    @2
    @0
    @14
    @17
    @37
    @1
    wceq
    @15
    @7
    @3
    cG
    @5
    @4
    @1
    @11
    @16
    @31
    @36
    grplinv
    sylan
    @33
    @1
    @2
    @7
    @35
    @0
    @30
    @17
    @32
    adantr
    erref
    eqbrtrd
    qusgrp2
    simpld
end
