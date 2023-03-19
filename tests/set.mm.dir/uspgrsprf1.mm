include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "uspgrsprf.mm"
include "wcel.mm"
include "wa.mm"
include "c2nd.mm"
include "uspgrsprfv.mm"
include "eqeqan12d.mm"
include "cop.mm"
include "cvtx.mm"
include "cedg.mm"
include "cuspgr.mm"
include "wrex.mm"
include "wex.mm"
include "copab.mm"
include "eleq2i.mm"
include "elopab.mm"
include "opeq12.mm"
include "eqeq2d.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "eqeq2.mm"
include "bi2anan9.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "cbvex2v.mm"
include "3bitri.mm"
include "bitri.mm"
include "ex.mm"
include "equcoms.mm"
include "syl6bir.mm"
include "ad2antrl.mm"
include "com12.mm"
include "imp.mm"
include "vex.mm"
include "op2ndd.mm"
include "eqeq12d.mm"
include "eqeq12.mm"
include "3imtr4d.mm"
include "exlimivv.mm"
include "syl2anb.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem uspgrsprf1
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  let vq: setvar q
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }
  assume uspgrsprf.f: |- F = ( g e. G |-> ( 2nd ` g ) )

  disjoint P e
  disjoint P g
  disjoint P v
  disjoint e g
  disjoint e v
  disjoint g v
  disjoint G g
  disjoint V e
  disjoint V v
  disjoint V q
  disjoint P e
  disjoint P q
  disjoint P v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V e
  disjoint V q
  disjoint V v
  disjoint G g
  disjoint X g
  disjoint F a
  disjoint F b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint a g
  disjoint b g
  disjoint P a
  disjoint P b
  disjoint V a
  disjoint V b
  disjoint V f
  disjoint V w
  disjoint a f
  disjoint a e
  disjoint a v
  disjoint a w
  disjoint b f
  disjoint b e
  disjoint b v
  disjoint b w
  disjoint e f
  disjoint f v
  disjoint f w
  disjoint e w
  disjoint v w
  disjoint f q
  disjoint q w
  disjoint W e
  disjoint W v
  disjoint k x
  assert |- F : G -1-1-> P

  proof
    cG
    cP
    cF
    wf1
    cG
    cP
    cF
    wf
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    cG
    wral
    va
    cG
    wral
    vv
    cP
    ve
    vg
    cF
    cG
    cV
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrsprf.f
    uspgrsprf
    @6
    va
    vb
    cG
    @0
    cG
    wcel
    #
    @2
    cG
    wcel
    #
    wa
    @4
    @0
    c2nd
    cfv
    #
    @2
    c2nd
    cfv
    #
    wceq
    #
    @5
    @7
    @8
    @1
    @9
    @3
    @10
    vv
    cP
    ve
    vg
    cF
    cG
    cV
    @0
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrsprf.f
    uspgrsprfv
    vv
    cP
    ve
    vg
    cF
    cG
    cV
    @2
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrsprf.f
    uspgrsprfv
    eqeqan12d
    @7
    @0
    vw
    cv
    #
    vf
    cv
    #
    cop
    #
    wceq
    #
    @12
    cV
    wceq
    #
    vq
    cv
    #
    cvtx
    cfv
    #
    @12
    wceq
    #
    @17
    cedg
    cfv
    #
    @13
    wceq
    #
    wa
    #
    vq
    cuspgr
    wrex
    #
    wa
    #
    wa
    #
    vf
    wex
    vw
    wex
    #
    @2
    vv
    cv
    #
    ve
    cv
    #
    cop
    #
    wceq
    #
    @27
    cV
    wceq
    #
    @18
    @27
    wceq
    #
    @20
    @28
    wceq
    #
    wa
    #
    vq
    cuspgr
    wrex
    #
    wa
    #
    wa
    #
    ve
    wex
    vv
    wex
    #
    @11
    @5
    wi
    #
    @8
    @7
    @0
    @36
    vv
    ve
    copab
    #
    wcel
    @0
    @29
    wceq
    #
    @36
    wa
    #
    ve
    wex
    vv
    wex
    @26
    cG
    @40
    @0
    uspgrsprf.g
    eleq2i
    @36
    vv
    ve
    @0
    elopab
    @42
    @25
    vv
    ve
    vw
    vf
    vv
    vw
    weq
    #
    ve
    vf
    weq
    #
    wa
    #
    @41
    @15
    @36
    @24
    @45
    @29
    @14
    @0
    @27
    @28
    @12
    @13
    opeq12
    eqeq2d
    @45
    @31
    @16
    @35
    @23
    @43
    @31
    @16
    wb
    @44
    @27
    @12
    cV
    eqeq1
    adantr
    @45
    @34
    @22
    vq
    cuspgr
    @43
    @32
    @19
    @44
    @33
    @21
    @27
    @12
    @18
    eqeq2
    @28
    @13
    @20
    eqeq2
    bi2anan9
    rexbidv
    anbi12d
    anbi12d
    cbvex2v
    3bitri
    @8
    @2
    @40
    wcel
    @38
    cG
    @40
    @2
    uspgrsprf.g
    eleq2i
    @36
    vv
    ve
    @2
    elopab
    bitri
    @26
    @38
    @39
    @25
    @38
    @39
    wi
    vw
    vf
    @38
    @25
    @39
    @37
    @25
    @39
    wi
    vv
    ve
    @37
    @25
    @39
    @37
    @25
    wa
    #
    vf
    ve
    weq
    #
    @14
    @29
    wceq
    #
    @11
    @5
    @37
    @25
    @47
    @48
    wi
    #
    @31
    @25
    @49
    wi
    @30
    @35
    @25
    @31
    @49
    @16
    @31
    @49
    wi
    @15
    @23
    @16
    @31
    @43
    @49
    @12
    cV
    @27
    eqeq2
    @49
    vw
    vv
    vw
    vv
    weq
    @47
    @48
    @12
    @13
    @27
    @28
    opeq12
    ex
    equcoms
    syl6bir
    ad2antrl
    com12
    ad2antrl
    imp
    @46
    @9
    @13
    @10
    @28
    @15
    @9
    @13
    wceq
    @37
    @24
    @12
    @13
    @0
    vw
    vex
    vf
    vex
    op2ndd
    ad2antrl
    @37
    @10
    @28
    wceq
    #
    @25
    @30
    @50
    @36
    @27
    @28
    @2
    vv
    vex
    ve
    vex
    op2ndd
    adantr
    adantr
    eqeq12d
    @37
    @25
    @5
    @48
    wb
    #
    @30
    @25
    @51
    wi
    @36
    @25
    @30
    @51
    @15
    @30
    @51
    wi
    @24
    @15
    @30
    @51
    @0
    @14
    @2
    @29
    eqeq12
    ex
    adantr
    com12
    adantr
    imp
    3imtr4d
    ex
    exlimivv
    com12
    exlimivv
    imp
    syl2anb
    sylbid
    rgen2a
    va
    vb
    cG
    cP
    cF
    dff13
    mpbir2an
end
