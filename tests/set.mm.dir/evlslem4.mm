include "co.mm"
include "cmpt2.mm"
include "csupp.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmpt.mm"
include "c2nd.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfov.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveqan12d.mm"
include "cbvmpt2.mm"
include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "vex.mm"
include "eqop2.mm"
include "adantl.mm"
include "sylbi.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"
include "w3a.mm"
include "simp2.mm"
include "3adant3.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "simp3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "mpt2eq3dva.mm"
include "syl5reqr.mm"
include "oveq1d.mm"
include "cdif.mm"
include "wo.mm"
include "cun.mm"
include "difxp.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"
include "xp1st.mm"
include "fmptd.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "sylan2.mm"
include "crg.mm"
include "adantr.mm"
include "wf.mm"
include "xp2nd.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ringlz.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "xpexg.mm"
include "suppss2.mm"
include "eqsstrd.mm"

theorem evlslem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vz: setvar z
  assume evlslem4.b: |- B = ( Base ` R )
  assume evlslem4.z: |- .0. = ( 0g ` R )
  assume evlslem4.t: |- .x. = ( .r ` R )
  assume evlslem4.r: |- ( ph -> R e. Ring )
  assume evlslem4.x: |- ( ( ph /\ x e. I ) -> X e. B )
  assume evlslem4.y: |- ( ( ph /\ y e. J ) -> Y e. B )
  assume evlslem4.i: |- ( ph -> I e. V )
  assume evlslem4.j: |- ( ph -> J e. W )

  disjoint x y
  disjoint I x
  disjoint I y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint X y
  disjoint B x
  disjoint B y
  disjoint .x. x
  disjoint .x. y
  disjoint Y x
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint x z
  disjoint y z
  disjoint I z
  disjoint J i
  disjoint J j
  disjoint J z
  disjoint ph z
  disjoint X i
  disjoint X j
  disjoint X z
  disjoint .0. z
  disjoint .x. i
  disjoint .x. j
  disjoint .x. z
  disjoint Y i
  disjoint Y j
  disjoint Y z
  assert |- ( ph -> ( ( x e. I , y e. J |-> ( X .x. Y ) ) supp .0. ) C_ ( ( ( x e. I |-> X ) supp .0. ) X. ( ( y e. J |-> Y ) supp .0. ) ) )

  proof
    wph
    vx
    vy
    cI
    cJ
    cX
    cY
    c.x
    co
    #
    cmpt2
    #
    c.0
    csupp
    co
    vz
    cI
    cJ
    cxp
    #
    vz
    cv
    #
    c1st
    cfv
    #
    vx
    cI
    cX
    cmpt
    #
    cfv
    #
    @3
    c2nd
    cfv
    #
    vy
    cJ
    cY
    cmpt
    #
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    c.0
    csupp
    co
    @5
    c.0
    csupp
    co
    #
    @8
    c.0
    csupp
    co
    #
    cxp
    #
    wph
    @1
    @11
    c.0
    csupp
    wph
    @11
    vx
    vy
    cI
    cJ
    vx
    cv
    #
    @5
    cfv
    #
    vy
    cv
    #
    @8
    cfv
    #
    c.x
    co
    #
    cmpt2
    #
    @1
    @20
    vi
    vj
    cI
    cJ
    vi
    cv
    #
    @5
    cfv
    #
    vj
    cv
    #
    @8
    cfv
    #
    c.x
    co
    #
    cmpt2
    @11
    vx
    vy
    vi
    vj
    cI
    cJ
    @19
    @25
    vi
    @19
    nfcv
    vj
    @19
    nfcv
    vx
    @22
    @24
    c.x
    vx
    cI
    cX
    @21
    nffvmpt1
    vx
    c.x
    nfcv
    vx
    @24
    nfcv
    nfov
    vy
    @22
    @24
    c.x
    vy
    @22
    nfcv
    vy
    c.x
    nfcv
    vy
    cJ
    cY
    @23
    nffvmpt1
    nfov
    @15
    @21
    wceq
    @17
    @23
    wceq
    @16
    @22
    @18
    @24
    c.x
    @15
    @21
    @5
    fveq2
    @17
    @23
    @8
    fveq2
    oveqan12d
    cbvmpt2
    vi
    vj
    vz
    cI
    cJ
    @10
    @25
    @3
    @21
    @23
    cop
    wceq
    @3
    cvv
    cvv
    cxp
    wcel
    #
    @4
    @21
    wceq
    #
    @7
    @23
    wceq
    #
    wa
    #
    wa
    @10
    @25
    wceq
    #
    @3
    @21
    @23
    vi
    vex
    vj
    vex
    eqop2
    @29
    @30
    @26
    @27
    @28
    @6
    @22
    @9
    @24
    c.x
    @4
    @21
    @5
    fveq2
    @7
    @23
    @8
    fveq2
    oveqan12d
    adantl
    sylbi
    mpt2mpt
    eqtr4i
    wph
    vx
    vy
    cI
    cJ
    @19
    @0
    wph
    @15
    cI
    wcel
    #
    @17
    cJ
    wcel
    #
    w3a
    #
    @16
    cX
    @18
    cY
    c.x
    @33
    @31
    cX
    cB
    wcel
    #
    @16
    cX
    wceq
    wph
    @31
    @32
    simp2
    wph
    @31
    @34
    @32
    evlslem4.x
    3adant3
    vx
    cI
    cX
    cB
    @5
    @5
    eqid
    #
    fvmpt2
    syl2anc
    @33
    @32
    cY
    cB
    wcel
    #
    @18
    cY
    wceq
    wph
    @31
    @32
    simp3
    wph
    @32
    @36
    @31
    evlslem4.y
    3adant2
    vy
    cJ
    cY
    cB
    @8
    @8
    eqid
    #
    fvmpt2
    syl2anc
    oveq12d
    mpt2eq3dva
    syl5reqr
    oveq1d
    wph
    @2
    @10
    vz
    cvv
    @14
    c.0
    @3
    @2
    @14
    cdif
    #
    wcel
    #
    wph
    @3
    cI
    @12
    cdif
    #
    cJ
    cxp
    #
    wcel
    #
    @3
    cI
    cJ
    @13
    cdif
    #
    cxp
    #
    wcel
    #
    wo
    #
    @10
    c.0
    wceq
    #
    @39
    @3
    @41
    @44
    cun
    #
    wcel
    @46
    @38
    @48
    @3
    @12
    @13
    cI
    cJ
    difxp
    eleq2i
    @3
    @41
    @44
    elun
    bitri
    wph
    @42
    @47
    @45
    wph
    @42
    wa
    #
    @10
    c.0
    @9
    c.x
    co
    #
    c.0
    @49
    @6
    c.0
    @9
    c.x
    @42
    wph
    @4
    @40
    wcel
    @6
    c.0
    wceq
    @3
    @40
    cJ
    xp1st
    wph
    cI
    cB
    cvv
    @5
    cV
    @12
    @4
    c.0
    wph
    vx
    cI
    cX
    cB
    @5
    evlslem4.x
    @35
    fmptd
    #
    @12
    @12
    wss
    wph
    @12
    ssid
    a1i
    evlslem4.i
    c.0
    cvv
    wcel
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    evlslem4.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    #
    suppssr
    sylan2
    oveq1d
    @49
    cR
    crg
    wcel
    #
    @9
    cB
    wcel
    #
    @50
    c.0
    wceq
    wph
    @53
    @42
    evlslem4.r
    adantr
    wph
    cJ
    cB
    @8
    wf
    @7
    cJ
    wcel
    @54
    @42
    wph
    vy
    cJ
    cY
    cB
    @8
    evlslem4.y
    @37
    fmptd
    #
    @3
    @40
    cJ
    xp2nd
    cJ
    cB
    @7
    @8
    ffvelrn
    syl2an
    cB
    cR
    c.x
    @9
    c.0
    evlslem4.b
    evlslem4.t
    evlslem4.z
    ringlz
    syl2anc
    eqtrd
    wph
    @45
    wa
    #
    @10
    @6
    c.0
    c.x
    co
    #
    c.0
    @56
    @9
    c.0
    @6
    c.x
    @45
    wph
    @7
    @43
    wcel
    @9
    c.0
    wceq
    @3
    cI
    @43
    xp2nd
    wph
    cJ
    cB
    cvv
    @8
    cW
    @13
    @7
    c.0
    @55
    @13
    @13
    wss
    wph
    @13
    ssid
    a1i
    evlslem4.j
    @52
    suppssr
    sylan2
    oveq2d
    @56
    @53
    @6
    cB
    wcel
    #
    @57
    c.0
    wceq
    wph
    @53
    @45
    evlslem4.r
    adantr
    wph
    cI
    cB
    @5
    wf
    @4
    cI
    wcel
    @58
    @45
    @51
    @3
    cI
    @43
    xp1st
    cI
    cB
    @4
    @5
    ffvelrn
    syl2an
    cB
    cR
    c.x
    @6
    c.0
    evlslem4.b
    evlslem4.t
    evlslem4.z
    ringrz
    syl2anc
    eqtrd
    jaodan
    sylan2b
    wph
    cI
    cV
    wcel
    cJ
    cW
    wcel
    @2
    cvv
    wcel
    evlslem4.i
    evlslem4.j
    cI
    cJ
    cV
    cW
    xpexg
    syl2anc
    suppss2
    eqsstrd
end
