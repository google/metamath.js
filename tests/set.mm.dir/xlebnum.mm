include "cv.mm"
include "co.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt2.mm"
include "cbl.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "crp.mm"
include "cmopn.mm"
include "eqid.mm"
include "cxmt.mm"
include "wcel.mm"
include "cme.mm"
include "1rp.mm"
include "stdbdmet.mm"
include "sylancl.mm"
include "ccmp.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wceq.mm"
include "rpxr.mm"
include "mp1i.mm"
include "0lt1.mm"
include "a1i.mm"
include "stdbdmopn.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "sseqtrd.mm"
include "lebnum.mm"
include "wa.mm"
include "simpr.mm"
include "ifcl.mm"
include "wi.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "syl.mm"
include "cr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "1re.mm"
include "min2.mm"
include "stdbdbl.mm"
include "syl33anc.mm"
include "metxmet.mm"
include "min1.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "eqsstr3d.mm"
include "sstr2.mm"
include "reximdv.mm"
include "ralimdva.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem xlebnum
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cD: class D
  let cU: class U
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  assume xlebnum.j: |- J = ( MetOpen ` D )
  assume xlebnum.d: |- ( ph -> D e. ( *Met ` X ) )
  assume xlebnum.c: |- ( ph -> J e. Comp )
  assume xlebnum.s: |- ( ph -> U C_ J )
  assume xlebnum.u: |- ( ph -> X = U. U )

  disjoint d u
  disjoint d x
  disjoint D d
  disjoint u x
  disjoint D u
  disjoint D x
  disjoint ph u
  disjoint ph x
  disjoint U d
  disjoint U u
  disjoint U x
  disjoint X d
  disjoint X u
  disjoint X x
  disjoint d r
  disjoint d y
  disjoint d z
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint ph r
  disjoint U r
  disjoint X r
  disjoint X y
  disjoint X z
  assert |- ( ph -> E. d e. RR+ A. x e. X E. u e. U ( x ( ball ` D ) d ) C_ u )

  proof
    wph
    vx
    cv
    #
    vr
    cv
    #
    vy
    vz
    cX
    cX
    vy
    cv
    vz
    cv
    cD
    co
    #
    c1
    cle
    wbr
    @2
    c1
    cif
    cmpt2
    #
    cbl
    cfv
    #
    co
    #
    vu
    cv
    #
    wss
    #
    vu
    cU
    wrex
    #
    vx
    cX
    wral
    #
    vr
    crp
    wrex
    @0
    vd
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @6
    wss
    #
    vu
    cU
    wrex
    #
    vx
    cX
    wral
    #
    vd
    crp
    wrex
    #
    wph
    vx
    vu
    @3
    cU
    @3
    cmopn
    cfv
    #
    cX
    vr
    @17
    eqid
    wph
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    c1
    crp
    wcel
    #
    @3
    cX
    cme
    cfv
    wcel
    #
    xlebnum.d
    1rp
    vy
    vz
    cD
    @3
    c1
    cX
    @3
    eqid
    #
    stdbdmet
    sylancl
    #
    wph
    cJ
    @17
    ccmp
    wph
    @19
    c1
    cxr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    cJ
    @17
    wceq
    xlebnum.d
    @20
    @24
    wph
    1rp
    c1
    rpxr
    #
    mp1i
    @25
    wph
    0lt1
    a1i
    vy
    vz
    cD
    @3
    c1
    cJ
    cX
    @22
    xlebnum.j
    stdbdmopn
    syl3anc
    #
    xlebnum.c
    eqeltrrd
    wph
    cU
    cJ
    @17
    xlebnum.s
    @27
    sseqtrd
    xlebnum.u
    lebnum
    wph
    @9
    @16
    vr
    crp
    wph
    @1
    crp
    wcel
    #
    wa
    #
    @1
    c1
    cle
    wbr
    #
    @1
    c1
    cif
    #
    crp
    wcel
    #
    @9
    @0
    @31
    @11
    co
    #
    @6
    wss
    #
    vu
    cU
    wrex
    #
    vx
    cX
    wral
    #
    @16
    @29
    @28
    @20
    @32
    wph
    @28
    simpr
    1rp
    @30
    @1
    c1
    crp
    ifcl
    sylancl
    #
    @29
    @8
    @35
    vx
    cX
    @29
    @0
    cX
    wcel
    #
    wa
    #
    @7
    @34
    vu
    cU
    @39
    @33
    @5
    wss
    @7
    @34
    wi
    @39
    @33
    @0
    @31
    @4
    co
    #
    @5
    @39
    @19
    @24
    @25
    @38
    @31
    cxr
    wcel
    #
    @31
    c1
    cle
    wbr
    #
    @40
    @33
    wceq
    wph
    @19
    @28
    @38
    xlebnum.d
    ad2antrr
    @20
    @24
    @39
    1rp
    @26
    mp1i
    @25
    @39
    0lt1
    a1i
    @29
    @38
    simpr
    #
    @39
    @32
    @41
    @29
    @32
    @38
    @37
    adantr
    @31
    rpxr
    syl
    #
    @39
    @1
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @42
    @28
    @45
    wph
    @38
    @1
    rpre
    ad2antlr
    #
    1re
    @1
    c1
    min2
    sylancl
    vy
    vz
    cD
    @3
    @0
    c1
    @31
    cX
    @22
    stdbdbl
    syl33anc
    @39
    @3
    @18
    wcel
    #
    @38
    @41
    @1
    cxr
    wcel
    #
    @31
    @1
    cle
    wbr
    #
    @40
    @5
    wss
    @39
    @21
    @48
    wph
    @21
    @28
    @38
    @23
    ad2antrr
    @3
    cX
    metxmet
    syl
    @43
    @44
    @28
    @49
    wph
    @38
    @1
    rpxr
    ad2antlr
    @39
    @45
    @46
    @50
    @47
    1re
    @1
    c1
    min1
    sylancl
    @3
    @0
    @31
    @1
    cX
    ssbl
    syl221anc
    eqsstr3d
    @33
    @5
    @6
    sstr2
    syl
    reximdv
    ralimdva
    @15
    @36
    vd
    @31
    crp
    @10
    @31
    wceq
    #
    @14
    @35
    vx
    cX
    @51
    @13
    @34
    vu
    cU
    @51
    @12
    @33
    @6
    @10
    @31
    @0
    @11
    oveq2
    sseq1d
    rexbidv
    ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
end
