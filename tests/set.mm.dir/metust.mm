include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfg.mm"
include "co.mm"
include "cust.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrex.mm"
include "w3a.mm"
include "cfbas.mm"
include "cfil.mm"
include "metustfbas.mm"
include "fgcl.mm"
include "filsspw.mm"
include "3syl.mm"
include "filtop.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "elpwid.mm"
include "simpr.mm"
include "filss.mm"
include "syl13anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "filin.mm"
include "syl3anc.mm"
include "metustid.mm"
include "ad5ant24.mm"
include "sstrd.mm"
include "elfg.mm"
include "biimpa.mm"
include "simprd.mm"
include "sylan.mm"
include "r19.29a.mm"
include "adantr.mm"
include "ssfg.mm"
include "sseldd.mm"
include "simpld.mm"
include "cnvss.mm"
include "cnvxp.mm"
include "syl6sseq.mm"
include "wceq.mm"
include "metustsym.mm"
include "adantl.mm"
include "eqsstr3d.mm"
include "metustexhalf.mm"
include "ad4ant13.mm"
include "r19.41v.mm"
include "sstr.mm"
include "reximi.mm"
include "sylbir.mm"
include "syl2anc.mm"
include "ssrexv.mm"
include "sylc.mm"
include "3jca.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "isust.mm"
include "mpbir3and.mm"

theorem metust
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
  let cA: class A
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vr: setvar r
  let vv: setvar v
  let vu: setvar u
  let vw: setvar w
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint D a
  disjoint X a
  disjoint F a
  disjoint B a
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  disjoint a p
  disjoint a q
  disjoint b p
  disjoint b q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint a x
  disjoint p x
  disjoint D p
  disjoint q x
  disjoint D q
  disjoint D x
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X p
  disjoint X q
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint a r
  disjoint a v
  disjoint p r
  disjoint p v
  disjoint q r
  disjoint q v
  disjoint r v
  disjoint A r
  disjoint A v
  disjoint a u
  disjoint a w
  disjoint r u
  disjoint r w
  disjoint D r
  disjoint u v
  disjoint u w
  disjoint D u
  disjoint v w
  disjoint D v
  disjoint D w
  disjoint F r
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint X r
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint a y
  disjoint D y
  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> ( ( X X. X ) filGen F ) e. ( UnifOn ` X ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    wa
    #
    cX
    cX
    cxp
    #
    cF
    cfg
    co
    #
    cX
    cust
    cfv
    wcel
    #
    @4
    @3
    cpw
    #
    wss
    #
    @3
    @4
    wcel
    #
    vv
    cv
    #
    vw
    cv
    #
    wss
    #
    @10
    @4
    wcel
    #
    wi
    #
    vw
    @6
    wral
    #
    @9
    @10
    cin
    @4
    wcel
    #
    vw
    @4
    wral
    #
    cid
    cX
    cres
    #
    @9
    wss
    #
    @9
    ccnv
    #
    @4
    wcel
    #
    @10
    @10
    ccom
    #
    @9
    wss
    #
    vw
    @4
    wrex
    #
    w3a
    #
    w3a
    #
    vv
    @4
    wral
    #
    @2
    cF
    @3
    cfbas
    cfv
    wcel
    #
    @4
    @3
    cfil
    cfv
    wcel
    #
    @7
    cD
    cF
    cX
    va
    metust.1
    metustfbas
    #
    cF
    @3
    fgcl
    #
    @4
    @3
    filsspw
    3syl
    @2
    @27
    @28
    @8
    @29
    @30
    @4
    @3
    filtop
    3syl
    @2
    @25
    vv
    @4
    @2
    @9
    @4
    wcel
    #
    wa
    #
    @14
    @16
    @24
    @32
    @13
    vw
    @6
    @32
    @10
    @6
    wcel
    #
    wa
    #
    @11
    @12
    @34
    @11
    wa
    #
    @28
    @31
    @10
    @3
    wss
    @11
    @12
    @2
    @28
    @31
    @33
    @11
    @2
    @27
    @28
    @29
    @30
    syl
    #
    ad3antrrr
    @2
    @31
    @33
    @11
    simpllr
    @35
    @10
    @3
    @32
    @33
    @11
    simplr
    elpwid
    @34
    @11
    simpr
    @9
    @10
    @4
    @3
    filss
    syl13anc
    ex
    ralrimiva
    @32
    @15
    vw
    @4
    @32
    @12
    wa
    @28
    @31
    @12
    @15
    @2
    @28
    @31
    @12
    @36
    ad2antrr
    @2
    @31
    @12
    simplr
    @32
    @12
    simpr
    @9
    @10
    @4
    @3
    filin
    syl3anc
    ralrimiva
    @32
    @18
    @20
    @23
    @32
    vu
    cv
    #
    @9
    wss
    #
    @18
    vu
    cF
    @32
    @37
    cF
    wcel
    #
    wa
    #
    @38
    wa
    #
    @17
    @37
    @9
    @1
    @39
    @17
    @37
    wss
    @0
    @31
    @38
    @37
    cD
    cF
    cX
    va
    metust.1
    metustid
    ad5ant24
    @40
    @38
    simpr
    #
    sstrd
    @2
    @27
    @31
    @38
    vu
    cF
    wrex
    #
    @29
    @27
    @31
    wa
    #
    @9
    @3
    wss
    #
    @43
    @27
    @31
    @45
    @43
    wa
    vu
    @9
    cF
    @3
    elfg
    biimpa
    #
    simprd
    sylan
    #
    r19.29a
    @32
    @38
    @20
    vu
    cF
    @41
    @28
    @37
    @4
    wcel
    @19
    @3
    wss
    #
    @37
    @19
    wss
    @20
    @2
    @28
    @31
    @39
    @38
    @36
    ad3antrrr
    @41
    cF
    @4
    @37
    @32
    cF
    @4
    wss
    #
    @39
    @38
    @32
    @27
    @49
    @2
    @27
    @31
    @29
    adantr
    cF
    @3
    ssfg
    syl
    #
    ad2antrr
    @32
    @39
    @38
    simplr
    sseldd
    @41
    @45
    @48
    @32
    @45
    @39
    @38
    @2
    @27
    @31
    @45
    @29
    @44
    @45
    @43
    @46
    simpld
    sylan
    ad2antrr
    @45
    @19
    @3
    ccnv
    @3
    @9
    @3
    cnvss
    cX
    cX
    cnvxp
    syl6sseq
    syl
    @41
    @37
    @37
    ccnv
    #
    @19
    @1
    @39
    @51
    @37
    wceq
    @0
    @31
    @38
    @37
    cD
    cF
    cX
    va
    metust.1
    metustsym
    ad5ant24
    @38
    @51
    @19
    wss
    @40
    @37
    @9
    cnvss
    adantl
    eqsstr3d
    @37
    @19
    @4
    @3
    filss
    syl13anc
    @47
    r19.29a
    @32
    @49
    @22
    vw
    cF
    wrex
    #
    @23
    @50
    @32
    @38
    @52
    vu
    cF
    @41
    @21
    @37
    wss
    #
    vw
    cF
    wrex
    #
    @38
    @52
    @2
    @39
    @54
    @31
    @38
    vw
    @37
    cD
    cF
    cX
    va
    metust.1
    metustexhalf
    ad4ant13
    @42
    @54
    @38
    wa
    @53
    @38
    wa
    #
    vw
    cF
    wrex
    @52
    @53
    @38
    vw
    cF
    r19.41v
    @55
    @22
    vw
    cF
    @21
    @37
    @9
    sstr
    reximi
    sylbir
    syl2anc
    @47
    r19.29a
    @22
    vw
    cF
    @4
    ssrexv
    sylc
    3jca
    3jca
    ralrimiva
    @2
    cX
    cvv
    wcel
    #
    @5
    @7
    @8
    @26
    w3a
    wb
    @1
    @56
    @0
    cD
    cX
    cpsmet
    elfvex
    adantl
    vw
    vv
    @4
    cvv
    cX
    isust
    syl
    mpbir3and
end
