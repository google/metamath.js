include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "w3a.mm"
include "cfv.mm"
include "3coml.mm"
include "cle.mm"
include "cif.mm"
include "ifcl.mm"
include "adantl.mm"
include "wceq.mm"
include "simpll1.mm"
include "simprl.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "abssub.mm"
include "eqtrd.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "cr.mm"
include "wb.mm"
include "subcld.mm"
include "abscld.mm"
include "simplrl.mm"
include "rpred.mm"
include "simplrr.mm"
include "ltmin.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "simpl.mm"
include "syl6bi.mm"
include "simpll2.mm"
include "simprr.mm"
include "simpr.mm"
include "anim12d.mm"
include "fovcl.mm"
include "biimprd.mm"
include "imim12d.mm"
include "ralimdvva.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "rgen3.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "cnfldtopn.mm"
include "txmetcn.mm"
include "mp3an.mm"
include "mpbir2an.mm"

theorem addcnlem
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let c.pl: class .+
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vw: setvar w
  let vx: setvar x
  let cK: class K
  assume addcn.j: |- J = ( TopOpen ` CCfld )
  assume addcn.2: |- .+ : ( CC X. CC ) --> CC
  assume addcn.3: |- ( ( a e. RR+ /\ b e. CC /\ c e. CC ) -> E. y e. RR+ E. z e. RR+ A. u e. CC A. v e. CC ( ( ( abs ` ( u - b ) ) < y /\ ( abs ` ( v - c ) ) < z ) -> ( abs ` ( ( u .+ v ) - ( b .+ c ) ) ) < a ) )

  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint c u
  disjoint c v
  disjoint c y
  disjoint c z
  disjoint J c
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ u
  disjoint .+ v
  disjoint .+ y
  disjoint .+ z
  disjoint a w
  disjoint a x
  disjoint b w
  disjoint b x
  disjoint c w
  disjoint c x
  disjoint u w
  disjoint u x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x y
  disjoint x z
  disjoint J x
  disjoint K u
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint .+ x
  assert |- .+ e. ( ( J tX J ) Cn J )

  proof
    c.pl
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    #
    cc
    cc
    cxp
    cc
    c.pl
    wf
    #
    vb
    cv
    #
    vu
    cv
    #
    cabs
    cmin
    ccom
    #
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vc
    cv
    #
    vv
    cv
    #
    @4
    co
    #
    @6
    clt
    wbr
    #
    wa
    #
    @2
    @8
    c.pl
    co
    #
    @3
    @9
    c.pl
    co
    #
    @4
    co
    #
    va
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    #
    vx
    crp
    wrex
    #
    va
    crp
    wral
    vc
    cc
    wral
    vb
    cc
    wral
    #
    addcn.2
    @20
    vb
    vc
    va
    cc
    cc
    crp
    @2
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @16
    crp
    wcel
    #
    w3a
    #
    @3
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @9
    @8
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    wa
    #
    @14
    @13
    cmin
    co
    cabs
    cfv
    #
    @16
    clt
    wbr
    #
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    #
    vz
    crp
    wrex
    vy
    crp
    wrex
    #
    @20
    @24
    @22
    @23
    @39
    addcn.3
    3coml
    @25
    @38
    @20
    vy
    vz
    crp
    crp
    @25
    @28
    crp
    wcel
    #
    @32
    crp
    wcel
    #
    wa
    #
    wa
    #
    @28
    @32
    cle
    wbr
    #
    @28
    @32
    cif
    #
    crp
    wcel
    #
    @38
    @5
    @45
    clt
    wbr
    #
    @10
    @45
    clt
    wbr
    #
    wa
    #
    @17
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    #
    @20
    @42
    @46
    @25
    @44
    @28
    @32
    crp
    ifcl
    adantl
    @43
    @37
    @50
    vu
    vv
    cc
    cc
    @43
    @3
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    wa
    #
    wa
    #
    @49
    @34
    @36
    @17
    @55
    @47
    @29
    @48
    @33
    @55
    @47
    @29
    @27
    @32
    clt
    wbr
    #
    wa
    #
    @29
    @55
    @47
    @27
    @45
    clt
    wbr
    #
    @57
    @55
    @5
    @27
    @45
    clt
    @55
    @22
    @52
    @5
    @27
    wceq
    @22
    @23
    @24
    @42
    @54
    simpll1
    #
    @43
    @52
    @53
    simprl
    #
    @22
    @52
    wa
    @5
    @2
    @3
    cmin
    co
    cabs
    cfv
    @27
    @2
    @3
    @4
    @4
    eqid
    #
    cnmetdval
    @2
    @3
    abssub
    eqtrd
    syl2anc
    breq1d
    @55
    @27
    cr
    wcel
    @28
    cr
    wcel
    #
    @32
    cr
    wcel
    #
    @58
    @57
    wb
    @55
    @26
    @55
    @3
    @2
    @60
    @59
    subcld
    abscld
    @55
    @28
    @25
    @40
    @41
    @54
    simplrl
    rpred
    #
    @55
    @32
    @25
    @40
    @41
    @54
    simplrr
    rpred
    #
    @27
    @28
    @32
    ltmin
    syl3anc
    bitrd
    @29
    @56
    simpl
    syl6bi
    @55
    @48
    @31
    @28
    clt
    wbr
    #
    @33
    wa
    #
    @33
    @55
    @48
    @31
    @45
    clt
    wbr
    #
    @67
    @55
    @10
    @31
    @45
    clt
    @55
    @23
    @53
    @10
    @31
    wceq
    @22
    @23
    @24
    @42
    @54
    simpll2
    #
    @43
    @52
    @53
    simprr
    #
    @23
    @53
    wa
    @10
    @8
    @9
    cmin
    co
    cabs
    cfv
    @31
    @8
    @9
    @4
    @61
    cnmetdval
    @8
    @9
    abssub
    eqtrd
    syl2anc
    breq1d
    @55
    @31
    cr
    wcel
    @62
    @63
    @68
    @67
    wb
    @55
    @30
    @55
    @9
    @8
    @70
    @69
    subcld
    abscld
    @64
    @65
    @31
    @28
    @32
    ltmin
    syl3anc
    bitrd
    @66
    @33
    simpr
    syl6bi
    anim12d
    @55
    @17
    @36
    @55
    @15
    @35
    @16
    clt
    @55
    @13
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @15
    @35
    wceq
    @55
    @22
    @23
    @71
    @59
    @69
    @2
    @8
    cc
    cc
    cc
    c.pl
    addcn.2
    fovcl
    syl2anc
    @54
    @72
    @43
    @3
    @9
    cc
    cc
    cc
    c.pl
    addcn.2
    fovcl
    adantl
    @71
    @72
    wa
    @15
    @13
    @14
    cmin
    co
    cabs
    cfv
    @35
    @13
    @14
    @4
    @61
    cnmetdval
    @13
    @14
    abssub
    eqtrd
    syl2anc
    breq1d
    biimprd
    imim12d
    ralimdvva
    @19
    @51
    vx
    @45
    crp
    @6
    @45
    wceq
    #
    @18
    @50
    vu
    vv
    cc
    cc
    @73
    @12
    @49
    @17
    @73
    @7
    @47
    @11
    @48
    @6
    @45
    @5
    clt
    breq2
    @6
    @45
    @10
    clt
    breq2
    anbi12d
    imbi1d
    2ralbidv
    rspcev
    syl6an
    rexlimdvva
    mpd
    rgen3
    @4
    cc
    cxmt
    cfv
    wcel
    #
    @74
    @74
    @0
    @1
    @21
    wa
    wb
    cnxmet
    cnxmet
    cnxmet
    vb
    vc
    va
    vx
    vv
    vu
    @4
    @4
    @4
    c.pl
    cJ
    cJ
    cJ
    cc
    cc
    cc
    cJ
    addcn.j
    cnfldtopn
    #
    @75
    @75
    txmetcn
    mp3an
    mpbir2an
end
