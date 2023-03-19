include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cxr.mm"
include "wa.mm"
include "wcel.mm"
include "cle.mm"
include "ssel2.mm"
include "0xr.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "mp3an12.mm"
include "wb.mm"
include "iccssxr.mm"
include "sseli.mm"
include "xrlenlt.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl.mm"
include "ralrimiva.mm"
include "ad3antrrr.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "simplll.mm"
include "a1i.mm"
include "simplr.mm"
include "sseldi.mm"
include "simpllr.mm"
include "simpr.mm"
include "xrlelttrd.mm"
include "ex.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "syl5.mm"
include "adantll.mm"
include "imp.mm"
include "adantrl.mm"
include "an32s.mm"
include "0e0iccpnf.mm"
include "wceq.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "breq1.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpan.mm"
include "syl2anc.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "anim2d.mm"
include "adantr.mm"
include "weq.mm"
include "wo.mm"
include "xrletri.mm"
include "mpjaodan.mm"
include "sstr.mm"
include "mpan2.mm"
include "xrinfmss.mm"
include "r19.29a.mm"

theorem xrge0infss
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  assert |- ( A C_ ( 0 [,] +oo ) -> E. x e. ( 0 [,] +oo ) ( A. y e. A -. y < x /\ A. y e. ( 0 [,] +oo ) ( x < y -> E. z e. A z < y ) ) )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wss
    #
    vy
    cv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @3
    @2
    clt
    wbr
    #
    vz
    cv
    @2
    clt
    wbr
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cxr
    wral
    #
    wa
    #
    @2
    vx
    cv
    #
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @12
    @2
    clt
    wbr
    #
    @8
    wi
    #
    vy
    @0
    wral
    #
    wa
    #
    vx
    @0
    wrex
    #
    vw
    cxr
    @1
    @3
    cxr
    wcel
    #
    wa
    #
    @11
    wa
    #
    @3
    cc0
    cle
    wbr
    #
    @20
    cc0
    @3
    cle
    wbr
    #
    @23
    @24
    wa
    @2
    cc0
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    cc0
    @2
    clt
    wbr
    #
    @8
    wi
    #
    vy
    @0
    wral
    #
    @20
    @1
    @28
    @21
    @11
    @24
    @1
    @27
    vy
    cA
    @1
    @2
    cA
    wcel
    wa
    @2
    @0
    wcel
    #
    @27
    cA
    @0
    @2
    ssel2
    @32
    cc0
    @2
    cle
    wbr
    #
    @27
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    @32
    @33
    0xr
    pnfxr
    cc0
    cpnf
    @2
    iccgelb
    mp3an12
    @32
    @34
    @2
    cxr
    wcel
    @33
    @27
    wb
    0xr
    @0
    cxr
    @2
    cc0
    cpnf
    iccssxr
    #
    sseli
    cc0
    @2
    xrlenlt
    sylancr
    mpbid
    syl
    ralrimiva
    ad3antrrr
    @22
    @24
    @11
    @31
    @22
    @24
    wa
    #
    @10
    @31
    @6
    @36
    @10
    @31
    @21
    @24
    @10
    @31
    wi
    @1
    @10
    @9
    vy
    @0
    wral
    #
    @21
    @24
    wa
    #
    @31
    @0
    cxr
    wss
    #
    @10
    @37
    wi
    #
    @35
    @9
    vy
    @0
    cxr
    ssralv
    ax-mp
    #
    @38
    @9
    @30
    vy
    @0
    @38
    @32
    wa
    #
    @29
    @7
    @8
    @42
    @29
    @7
    @42
    @29
    wa
    #
    @3
    cc0
    @2
    @21
    @24
    @32
    @29
    simplll
    @34
    @43
    0xr
    a1i
    @43
    @0
    cxr
    @2
    @35
    @38
    @32
    @29
    simplr
    sseldi
    @21
    @24
    @32
    @29
    simpllr
    @42
    @29
    simpr
    xrlelttrd
    ex
    imim1d
    ralimdva
    syl5
    adantll
    imp
    adantrl
    an32s
    cc0
    @0
    wcel
    @28
    @31
    wa
    #
    @20
    0e0iccpnf
    @19
    @44
    vx
    cc0
    @0
    @12
    cc0
    wceq
    #
    @15
    @28
    @18
    @31
    @45
    @14
    @27
    vy
    cA
    @45
    @13
    @26
    @12
    cc0
    @2
    clt
    breq2
    notbid
    ralbidv
    @45
    @17
    @30
    vy
    @0
    @45
    @16
    @29
    @8
    @12
    cc0
    @2
    clt
    breq1
    imbi1d
    ralbidv
    anbi12d
    rspcev
    mpan
    syl2anc
    @23
    @25
    wa
    #
    @3
    @0
    wcel
    #
    @6
    @37
    wa
    #
    @20
    @46
    @21
    @25
    @47
    @1
    @21
    @11
    @25
    simpllr
    @23
    @25
    simpr
    @3
    elxrge0
    sylanbrc
    @23
    @48
    @25
    @22
    @11
    @48
    @1
    @11
    @48
    wi
    @21
    @1
    @10
    @37
    @6
    @40
    @1
    @41
    a1i
    anim2d
    adantr
    imp
    adantr
    @19
    @48
    vx
    @3
    @0
    vx
    vw
    weq
    #
    @15
    @6
    @18
    @37
    @49
    @14
    @5
    vy
    cA
    @49
    @13
    @4
    @12
    @3
    @2
    clt
    breq2
    notbid
    ralbidv
    @49
    @17
    @9
    vy
    @0
    @49
    @16
    @7
    @8
    @12
    @3
    @2
    clt
    breq1
    imbi1d
    ralbidv
    anbi12d
    rspcev
    syl2anc
    @23
    @21
    @34
    @24
    @25
    wo
    @1
    @21
    @11
    simplr
    @34
    @23
    0xr
    a1i
    @3
    cc0
    xrletri
    syl2anc
    mpjaodan
    @1
    cA
    cxr
    wss
    #
    @11
    vw
    cxr
    wrex
    @1
    @39
    @50
    @35
    cA
    @0
    cxr
    sstr
    mpan2
    vw
    vy
    vz
    cA
    xrinfmss
    syl
    r19.29a
end
