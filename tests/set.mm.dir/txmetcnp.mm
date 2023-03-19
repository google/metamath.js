include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ctmt.mm"
include "cxps.mm"
include "co.mm"
include "cds.mm"
include "cmopn.mm"
include "ccnp.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ctx.mm"
include "wb.mm"
include "eqid.mm"
include "simpl1.mm"
include "simpl2.mm"
include "tmsxps.mm"
include "simpl3.mm"
include "opelxpi.mm"
include "adantl.mm"
include "metcnp.mm"
include "syl3anc.mm"
include "tmsxpsmopn.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "df-ov.mm"
include "oveq1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "syl5eqr.mm"
include "imbi12d.mm"
include "ralxp.mm"
include "cle.mm"
include "cif.mm"
include "ad2antrr.mm"
include "simpllr.mm"
include "simpld.mm"
include "simprd.mm"
include "simprrl.mm"
include "simprrr.mm"
include "tmsxpsval2.mm"
include "cxr.mm"
include "xmetcl.mm"
include "rpxr.mm"
include "ad2antrl.mm"
include "xrmaxlt.mm"
include "bitrd.mm"
include "imbi1d.mm"
include "anassrs.mm"
include "2ralbidva.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "3bitr3d.mm"

theorem txmetcnp
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  assume metcn.2: |- J = ( MetOpen ` C )
  assume metcn.4: |- K = ( MetOpen ` D )
  assume txmetcnp.4: |- L = ( MetOpen ` E )

  disjoint u v
  disjoint u w
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v z
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K z
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z z
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E z
  disjoint L w
  disjoint L z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint J t
  disjoint J x
  disjoint J y
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint Y t
  disjoint Y x
  disjoint Y y
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint B x
  disjoint E x
  disjoint E y
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint L t
  disjoint L x
  disjoint L y
  assert |- ( ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) /\ E e. ( *Met ` Z ) ) /\ ( A e. X /\ B e. Y ) ) -> ( F e. ( ( ( J tX K ) CnP L ) ` <. A , B >. ) <-> ( F : ( X X. Y ) --> Z /\ A. z e. RR+ E. w e. RR+ A. u e. X A. v e. Y ( ( ( A C u ) < w /\ ( B D v ) < w ) -> ( ( A F B ) E ( u F v ) ) < z ) ) ) )

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
    cE
    cZ
    cxmt
    cfv
    wcel
    #
    w3a
    #
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    wa
    #
    cF
    cA
    cB
    cop
    #
    cC
    ctmt
    cfv
    cD
    ctmt
    cfv
    cxps
    co
    cds
    cfv
    #
    cmopn
    cfv
    #
    cL
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    cX
    cY
    cxp
    #
    cZ
    cF
    wf
    #
    @8
    vx
    cv
    #
    @9
    co
    #
    vw
    cv
    #
    clt
    wbr
    #
    @8
    cF
    cfv
    #
    @16
    cF
    cfv
    #
    cE
    co
    #
    vz
    cv
    #
    clt
    wbr
    #
    wi
    #
    vx
    @14
    wral
    #
    vw
    crp
    wrex
    #
    vz
    crp
    wral
    #
    wa
    #
    cF
    @8
    cJ
    cK
    ctx
    co
    #
    cL
    ccnp
    co
    #
    cfv
    #
    wcel
    @15
    cA
    vu
    cv
    #
    cC
    co
    #
    @18
    clt
    wbr
    cB
    vv
    cv
    #
    cD
    co
    #
    @18
    clt
    wbr
    wa
    #
    cA
    cB
    cF
    co
    #
    @33
    @35
    cF
    co
    #
    cE
    co
    #
    @23
    clt
    wbr
    #
    wi
    #
    vv
    cY
    wral
    vu
    cX
    wral
    #
    vw
    crp
    wrex
    #
    vz
    crp
    wral
    #
    wa
    @7
    @9
    @14
    cxmt
    cfv
    wcel
    @2
    @8
    @14
    wcel
    #
    @13
    @29
    wb
    @7
    @9
    cC
    cD
    cX
    cY
    @9
    eqid
    #
    @0
    @1
    @2
    @6
    simpl1
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    tmsxps
    @0
    @1
    @2
    @6
    simpl3
    @6
    @46
    @3
    cA
    cB
    cX
    cY
    opelxpi
    adantl
    vz
    vw
    vx
    @9
    cE
    @8
    cF
    @10
    cL
    @14
    cZ
    @10
    eqid
    #
    txmetcnp.4
    metcnp
    syl3anc
    @7
    @12
    @32
    cF
    @7
    @8
    @11
    @31
    @7
    @10
    @30
    cL
    ccnp
    @7
    @9
    cJ
    cK
    @10
    cC
    cD
    cX
    cY
    @47
    @48
    @49
    metcn.2
    metcn.4
    @50
    tmsxpsmopn
    oveq1d
    fveq1d
    eleq2d
    @7
    @15
    @28
    @45
    @7
    @15
    wa
    #
    @27
    @44
    vz
    crp
    @51
    @26
    @43
    vw
    crp
    @26
    @8
    @33
    @35
    cop
    #
    @9
    co
    #
    @18
    clt
    wbr
    #
    @41
    wi
    #
    vv
    cY
    wral
    vu
    cX
    wral
    @51
    @18
    crp
    wcel
    #
    wa
    #
    @43
    @25
    @55
    vx
    vu
    vv
    cX
    cY
    @16
    @52
    wceq
    #
    @19
    @54
    @24
    @41
    @58
    @17
    @53
    @18
    clt
    @16
    @52
    @8
    @9
    oveq2
    breq1d
    @58
    @22
    @40
    @23
    clt
    @58
    @22
    @38
    @21
    cE
    co
    @40
    @38
    @20
    @21
    cE
    cA
    cB
    cF
    df-ov
    oveq1i
    @58
    @21
    @39
    @38
    cE
    @58
    @21
    @52
    cF
    cfv
    @39
    @16
    @52
    cF
    fveq2
    @33
    @35
    cF
    df-ov
    syl6eqr
    oveq2d
    syl5eqr
    breq1d
    imbi12d
    ralxp
    @57
    @55
    @42
    vu
    vv
    cX
    cY
    @51
    @56
    @33
    cX
    wcel
    #
    @35
    cY
    wcel
    #
    wa
    #
    @55
    @42
    wb
    @51
    @56
    @61
    wa
    #
    wa
    #
    @54
    @37
    @41
    @63
    @54
    @34
    @36
    cle
    wbr
    @36
    @34
    cif
    #
    @18
    clt
    wbr
    #
    @37
    @63
    @53
    @64
    @18
    clt
    @63
    cA
    cB
    @33
    @35
    @9
    cC
    cD
    cX
    cY
    @47
    @7
    @0
    @15
    @62
    @48
    ad2antrr
    #
    @7
    @1
    @15
    @62
    @49
    ad2antrr
    #
    @63
    @4
    @5
    @3
    @6
    @15
    @62
    simpllr
    #
    simpld
    #
    @63
    @4
    @5
    @68
    simprd
    #
    @51
    @56
    @59
    @60
    simprrl
    #
    @51
    @56
    @59
    @60
    simprrr
    #
    tmsxpsval2
    breq1d
    @63
    @34
    cxr
    wcel
    #
    @36
    cxr
    wcel
    #
    @18
    cxr
    wcel
    #
    @65
    @37
    wb
    @63
    @0
    @4
    @59
    @73
    @66
    @69
    @71
    cA
    @33
    cC
    cX
    xmetcl
    syl3anc
    @63
    @1
    @5
    @60
    @74
    @67
    @70
    @72
    cB
    @35
    cD
    cY
    xmetcl
    syl3anc
    @56
    @75
    @51
    @61
    @18
    rpxr
    ad2antrl
    @34
    @36
    @18
    xrmaxlt
    syl3anc
    bitrd
    imbi1d
    anassrs
    2ralbidva
    syl5bb
    rexbidva
    ralbidv
    pm5.32da
    3bitr3d
end
