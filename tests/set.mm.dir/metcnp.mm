include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cbl.mm"
include "cima.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "metcnp3.mm"
include "wb.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "ad2antlr.mm"
include "cxr.mm"
include "simpll1.mm"
include "simpll3.mm"
include "rpxr.mm"
include "ad2antll.mm"
include "blssm.mm"
include "syl3anc.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "elbl.mm"
include "imbi1d.mm"
include "impexp.mm"
include "simpl2.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "rpxrd.mm"
include "simpllr.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "ffvelrnda.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "imbi2d.mm"
include "pm5.74da.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "ralbidv2.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "ralbidva.mm"
include "pm5.32da.mm"

theorem metcnp
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let cZ: class Z
  let cA: class A
  let cB: class B
  let cE: class E
  let cL: class L
  assume metcn.2: |- J = ( MetOpen ` C )
  assume metcn.4: |- K = ( MetOpen ` D )

  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y y
  disjoint Y z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint P w
  disjoint P y
  disjoint P z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y x
  disjoint Z t
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint D u
  disjoint D v
  disjoint D x
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint L t
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) /\ P e. X ) -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. y e. RR+ E. z e. RR+ A. w e. X ( ( P C w ) < z -> ( ( F ` P ) D ( F ` w ) ) < y ) ) ) )

  proof
    cC
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cY
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    cX
    cY
    cF
    wf
    #
    cF
    cP
    vz
    cv
    #
    cC
    cbl
    cfv
    co
    #
    cima
    cP
    cF
    cfv
    #
    vy
    cv
    #
    cD
    cbl
    cfv
    co
    #
    wss
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wa
    @4
    cP
    vw
    cv
    #
    cC
    co
    @5
    clt
    wbr
    #
    @7
    @13
    cF
    cfv
    #
    cD
    co
    @8
    clt
    wbr
    #
    wi
    #
    vw
    cX
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wa
    vy
    vz
    cC
    cD
    cP
    cF
    cJ
    cK
    cX
    cY
    metcn.2
    metcn.4
    metcnp3
    @3
    @4
    @12
    @20
    @3
    @4
    wa
    #
    @11
    @19
    vy
    crp
    @21
    @8
    crp
    wcel
    #
    wa
    @10
    @18
    vz
    crp
    @21
    @22
    @5
    crp
    wcel
    #
    @10
    @18
    wb
    @21
    @22
    @23
    wa
    #
    wa
    #
    @10
    @15
    @9
    wcel
    #
    vw
    @6
    wral
    #
    @18
    @25
    cF
    wfun
    #
    @6
    cF
    cdm
    #
    wss
    @10
    @27
    wb
    @4
    @28
    @3
    @24
    cX
    cY
    cF
    ffun
    ad2antlr
    @25
    @6
    cX
    @29
    @25
    @0
    @2
    @5
    cxr
    wcel
    #
    @6
    cX
    wss
    @0
    @1
    @2
    @4
    @24
    simpll1
    #
    @0
    @1
    @2
    @4
    @24
    simpll3
    #
    @23
    @30
    @21
    @22
    @5
    rpxr
    ad2antll
    #
    cC
    cP
    @5
    cX
    blssm
    syl3anc
    @4
    @29
    cX
    wceq
    @3
    @24
    cX
    cY
    cF
    fdm
    ad2antlr
    sseqtr4d
    vw
    @6
    @9
    cF
    funimass4
    syl2anc
    @25
    @26
    @17
    vw
    @6
    cX
    @25
    @13
    @6
    wcel
    #
    @26
    wi
    @13
    cX
    wcel
    #
    @14
    wa
    #
    @26
    wi
    #
    @35
    @17
    wi
    #
    @25
    @34
    @36
    @26
    @25
    @0
    @2
    @30
    @34
    @36
    wb
    @31
    @32
    @33
    @13
    cC
    cP
    @5
    cX
    elbl
    syl3anc
    imbi1d
    @37
    @35
    @14
    @26
    wi
    #
    wi
    @25
    @38
    @35
    @14
    @26
    impexp
    @25
    @35
    @39
    @17
    @25
    @35
    wa
    #
    @26
    @16
    @14
    @40
    @1
    @8
    cxr
    wcel
    @7
    cY
    wcel
    @15
    cY
    wcel
    @26
    @16
    wb
    @21
    @1
    @24
    @35
    @0
    @1
    @2
    @4
    simpl2
    ad2antrr
    @40
    @8
    @21
    @22
    @23
    @35
    simplrl
    rpxrd
    @40
    cX
    cY
    cP
    cF
    @3
    @4
    @24
    @35
    simpllr
    @25
    @2
    @35
    @32
    adantr
    ffvelrnd
    @25
    cX
    cY
    @13
    cF
    @3
    @4
    @24
    simplr
    ffvelrnda
    @15
    cD
    @7
    @8
    cY
    elbl2
    syl22anc
    imbi2d
    pm5.74da
    syl5bb
    bitrd
    ralbidv2
    bitrd
    anassrs
    rexbidva
    ralbidva
    pm5.32da
    bitrd
end
