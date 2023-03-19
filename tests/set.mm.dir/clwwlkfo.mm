include "cn.mm"
include "wcel.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "clwwlkf.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cs1.mm"
include "cconcat.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cmin.mm"
include "cfzo.mm"
include "clsw.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "clwwlknp.mm"
include "simpr.mm"
include "simpl1.mm"
include "3simpc.mm"
include "adantr.mm"
include "clwwlkel.mm"
include "syl3anc.mm"
include "opeq2.mm"
include "eqcoms.mm"
include "oveq2d.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "simpll.mm"
include "fstwrdne0.mm"
include "ancoms.mm"
include "s1cld.mm"
include "jca.mm"
include "3ad2antl1.mm"
include "swrdccat1.mm"
include "syl.mm"
include "eqtr2d.mm"
include "ex.mm"
include "impcom.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "wb.mm"
include "clwwlkfv.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem clwwlkfo
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let vi: setvar i
  let cP: class P
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vp: setvar p
  assume clwwlkbij.d: |- D = { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) }
  assume clwwlkbij.f: |- F = ( t e. D |-> ( t substr <. 0 , N >. ) )

  disjoint G w
  disjoint N w
  disjoint D t
  disjoint G t
  disjoint t w
  disjoint N t
  disjoint G i
  disjoint N i
  disjoint P i
  disjoint P w
  disjoint i t
  disjoint W t
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint N x
  disjoint N y
  disjoint i x
  disjoint i y
  disjoint t x
  disjoint t y
  disjoint w x
  disjoint w y
  disjoint D p
  disjoint F p
  disjoint G p
  disjoint G x
  disjoint i p
  disjoint i w
  disjoint p w
  disjoint p x
  disjoint N p
  assert |- ( N e. NN -> F : D -onto-> ( N ClWWalksN G ) )

  proof
    cN
    cn
    wcel
    #
    cD
    cN
    cG
    cclwwlkn
    co
    #
    cF
    wf
    vp
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cD
    wrex
    #
    vp
    @1
    wral
    cD
    @1
    cF
    wfo
    vw
    vt
    cD
    cF
    cG
    cN
    clwwlkbij.d
    clwwlkbij.f
    clwwlkf
    @0
    @6
    vp
    @1
    @0
    @2
    @1
    wcel
    #
    wa
    #
    @6
    @2
    @3
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    wceq
    #
    vx
    cD
    wrex
    #
    @8
    @2
    cc0
    @2
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cD
    wcel
    #
    @2
    @15
    @9
    csubstr
    co
    #
    wceq
    #
    wa
    #
    @12
    @7
    @0
    @19
    @7
    @2
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @2
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vi
    cv
    #
    @2
    cfv
    @26
    c1
    caddc
    co
    @2
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    @2
    clsw
    cfv
    @13
    cpr
    @27
    wcel
    #
    w3a
    #
    @0
    @19
    wi
    vi
    @27
    cG
    cN
    @20
    @2
    @20
    eqid
    @27
    eqid
    clwwlknp
    @30
    @0
    @19
    @30
    @0
    wa
    #
    @16
    @18
    @31
    @0
    @25
    @28
    @29
    wa
    #
    @16
    @30
    @0
    simpr
    @25
    @28
    @29
    @0
    simpl1
    @30
    @32
    @0
    @25
    @28
    @29
    3simpc
    adantr
    vw
    cD
    @2
    vi
    cG
    cN
    clwwlkbij.d
    clwwlkel
    syl3anc
    @31
    @17
    @15
    cc0
    @23
    cop
    #
    csubstr
    co
    #
    @2
    @30
    @17
    @34
    wceq
    #
    @0
    @25
    @28
    @35
    @29
    @24
    @35
    @22
    @24
    @9
    @33
    @15
    csubstr
    @9
    @33
    wceq
    cN
    @23
    cN
    @23
    cc0
    opeq2
    eqcoms
    oveq2d
    adantl
    3ad2ant1
    adantr
    @31
    @22
    @14
    @21
    wcel
    #
    wa
    #
    @34
    @2
    wceq
    @25
    @28
    @0
    @37
    @29
    @25
    @0
    wa
    #
    @22
    @36
    @22
    @24
    @0
    simpll
    @38
    @13
    @20
    @0
    @25
    @13
    @20
    wcel
    cN
    @20
    @2
    fstwrdne0
    ancoms
    s1cld
    jca
    3ad2antl1
    @20
    @2
    @14
    swrdccat1
    syl
    eqtr2d
    jca
    ex
    syl
    impcom
    @11
    @18
    vx
    @15
    cD
    @3
    @15
    wceq
    @10
    @17
    @2
    @3
    @15
    @9
    csubstr
    oveq1
    eqeq2d
    rspcev
    syl
    @8
    @5
    @11
    vx
    cD
    @3
    cD
    wcel
    #
    @5
    @11
    wb
    @8
    @39
    @4
    @10
    @2
    vw
    vt
    cD
    cF
    cG
    cN
    @3
    clwwlkbij.d
    clwwlkbij.f
    clwwlkfv
    eqeq2d
    adantl
    rexbidva
    mpbird
    ralrimiva
    vx
    vp
    cD
    @1
    cF
    dffo3
    sylanbrc
end
