include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt2.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "eqid.mm"
include "dfii2.mm"
include "0red.mm"
include "1red.mm"
include "cr.mm"
include "halfre.mm"
include "0re.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "1re.mm"
include "halflt1.mm"
include "elicc2i.mm"
include "mpbir3an.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "htpyi.mm"
include "simprd.mm"
include "simpld.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantrl.mm"
include "simprl.mm"
include "oveq2d.mm"
include "2cn.mm"
include "2ne0.mm"
include "recidi.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "1m1e0.mm"
include "3eqtr4d.mm"
include "wss.mm"
include "retopon.mm"
include "iccssre.mm"
include "mp2an.mm"
include "resttopon.mm"
include "cnmpt2nd.mm"
include "cnmpt1st.mm"
include "cmpt.mm"
include "iihalf1cn.mm"
include "oveq2.mm"
include "cnmpt21.mm"
include "chtpy.mm"
include "htpycn.mm"
include "sseldd.mm"
include "cnmpt22f.mm"
include "iihalf2cn.mm"
include "cnmpt2pc.mm"
include "cnmptcom.mm"
include "syl5eqel.mm"
include "simpr.mm"
include "0elunit.mm"
include "syl6eqbr.mm"
include "iftrued.mm"
include "simpl.mm"
include "2t0e0.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "sylancl.mm"
include "1elunit.mm"
include "clt.mm"
include "wn.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "breq1d.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "2t1e2.mm"
include "2m1e1.mm"
include "ishtpyd.mm"

theorem htpycc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vz: setvar z
  assume htpycc.1: |- N = ( x e. X , y e. ( 0 [,] 1 ) |-> if ( y <_ ( 1 / 2 ) , ( x L ( 2 x. y ) ) , ( x M ( ( 2 x. y ) - 1 ) ) ) )
  assume htpycc.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume htpycc.4: |- ( ph -> F e. ( J Cn K ) )
  assume htpycc.5: |- ( ph -> G e. ( J Cn K ) )
  assume htpycc.6: |- ( ph -> H e. ( J Cn K ) )
  assume htpycc.7: |- ( ph -> L e. ( F ( J Htpy K ) G ) )
  assume htpycc.8: |- ( ph -> M e. ( G ( J Htpy K ) H ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint M x
  disjoint M y
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint L s
  disjoint M s
  disjoint X s
  disjoint X z
  disjoint F s
  disjoint H s
  disjoint N s
  disjoint ph s
  disjoint ph z
  assert |- ( ph -> N e. ( F ( J Htpy K ) H ) )

  proof
    wph
    cF
    cH
    cN
    cJ
    cK
    cX
    vs
    htpycc.2
    htpycc.4
    htpycc.6
    wph
    cN
    vx
    vy
    cX
    cc0
    c1
    cicc
    co
    #
    vy
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    vx
    cv
    #
    c2
    @1
    cmul
    co
    #
    cL
    co
    #
    @4
    @5
    c1
    cmin
    co
    #
    cM
    co
    #
    cif
    #
    cmpt2
    cJ
    cii
    ctx
    co
    cK
    ccn
    co
    #
    htpycc.1
    wph
    vy
    vx
    @9
    cii
    cJ
    cK
    @0
    cX
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    htpycc.2
    wph
    vy
    vx
    cc0
    @2
    c1
    @6
    cioo
    crn
    ctg
    cfv
    #
    @8
    cJ
    cK
    @11
    cc0
    @2
    cicc
    co
    #
    crest
    co
    #
    @11
    @2
    c1
    cicc
    co
    #
    crest
    co
    #
    cii
    cX
    @11
    eqid
    @13
    eqid
    #
    @15
    eqid
    #
    dfii2
    wph
    0red
    wph
    1red
    @2
    @0
    wcel
    #
    wph
    @18
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    @2
    c1
    cle
    wbr
    halfre
    cc0
    @2
    0re
    halfre
    halfgt0
    ltleii
    #
    @2
    c1
    halfre
    1re
    halflt1
    ltleii
    cc0
    c1
    @2
    0re
    1re
    elicc2i
    mpbir3an
    a1i
    htpycc.2
    wph
    @1
    @2
    wceq
    #
    @4
    cX
    wcel
    #
    wa
    wa
    #
    @4
    c1
    cL
    co
    #
    @4
    cc0
    cM
    co
    #
    @6
    @8
    wph
    @22
    @24
    @25
    wceq
    #
    @21
    wph
    vs
    cv
    #
    c1
    cL
    co
    #
    @27
    cc0
    cM
    co
    #
    wceq
    #
    vs
    cX
    wral
    @22
    @26
    wph
    @30
    vs
    cX
    wph
    @27
    cX
    wcel
    #
    wa
    #
    @28
    @27
    cG
    cfv
    #
    @29
    @32
    @27
    cc0
    cL
    co
    #
    @27
    cF
    cfv
    #
    wceq
    #
    @28
    @33
    wceq
    #
    wph
    @27
    cF
    cG
    cL
    cJ
    cK
    cX
    htpycc.2
    htpycc.4
    htpycc.5
    htpycc.7
    htpyi
    #
    simprd
    @32
    @29
    @33
    wceq
    #
    @27
    c1
    cM
    co
    #
    @27
    cH
    cfv
    #
    wceq
    #
    wph
    @27
    cG
    cH
    cM
    cJ
    cK
    cX
    htpycc.2
    htpycc.5
    htpycc.6
    htpycc.8
    htpyi
    #
    simpld
    eqtr4d
    ralrimiva
    @30
    @26
    vs
    @4
    cX
    vs
    vx
    weq
    @28
    @24
    @29
    @25
    @27
    @4
    c1
    cL
    oveq1
    @27
    @4
    cc0
    cM
    oveq1
    eqeq12d
    rspccva
    sylan
    adantrl
    @23
    @5
    c1
    @4
    cL
    @23
    @5
    c2
    @2
    cmul
    co
    c1
    @23
    @1
    @2
    c2
    cmul
    wph
    @21
    @22
    simprl
    oveq2d
    c2
    2cn
    2ne0
    recidi
    syl6eq
    #
    oveq2d
    @23
    @7
    cc0
    @4
    cM
    @23
    @7
    c1
    c1
    cmin
    co
    cc0
    @23
    @5
    c1
    c1
    cmin
    @44
    oveq1d
    1m1e0
    syl6eq
    oveq2d
    3eqtr4d
    wph
    vy
    vx
    @4
    @5
    cL
    @13
    cJ
    cJ
    cii
    cK
    @12
    cX
    @13
    @12
    ctopon
    cfv
    wcel
    #
    wph
    @11
    cr
    ctopon
    cfv
    wcel
    #
    @12
    cr
    wss
    #
    @45
    retopon
    cc0
    cr
    wcel
    @19
    @47
    0re
    halfre
    cc0
    @2
    iccssre
    mp2an
    @12
    @11
    cr
    resttopon
    mp2an
    a1i
    #
    htpycc.2
    wph
    vy
    vx
    @13
    cJ
    @12
    cX
    @48
    htpycc.2
    cnmpt2nd
    wph
    vy
    vx
    vz
    @1
    c2
    vz
    cv
    #
    cmul
    co
    #
    @5
    @13
    cJ
    @13
    cii
    @12
    cX
    @12
    @48
    htpycc.2
    wph
    vy
    vx
    @13
    cJ
    @12
    cX
    @48
    htpycc.2
    cnmpt1st
    @48
    vz
    @12
    @50
    cmpt
    @13
    cii
    ccn
    co
    wcel
    wph
    vz
    @13
    @16
    iihalf1cn
    a1i
    @49
    @1
    c2
    cmul
    oveq2
    #
    cnmpt21
    wph
    cF
    cG
    cJ
    cK
    chtpy
    co
    #
    co
    @10
    cL
    wph
    cF
    cG
    cJ
    cK
    cX
    htpycc.2
    htpycc.4
    htpycc.5
    htpycn
    htpycc.7
    sseldd
    cnmpt22f
    wph
    vy
    vx
    @4
    @7
    cM
    @15
    cJ
    cJ
    cii
    cK
    @14
    cX
    @15
    @14
    ctopon
    cfv
    wcel
    #
    wph
    @46
    @14
    cr
    wss
    #
    @53
    retopon
    @19
    c1
    cr
    wcel
    @54
    halfre
    1re
    @2
    c1
    iccssre
    mp2an
    @14
    @11
    cr
    resttopon
    mp2an
    a1i
    #
    htpycc.2
    wph
    vy
    vx
    @15
    cJ
    @14
    cX
    @55
    htpycc.2
    cnmpt2nd
    wph
    vy
    vx
    vz
    @1
    @50
    c1
    cmin
    co
    #
    @7
    @15
    cJ
    @15
    cii
    @14
    cX
    @14
    @55
    htpycc.2
    wph
    vy
    vx
    @15
    cJ
    @14
    cX
    @55
    htpycc.2
    cnmpt1st
    @55
    vz
    @14
    @56
    cmpt
    @15
    cii
    ccn
    co
    wcel
    wph
    vz
    @15
    @17
    iihalf2cn
    a1i
    vz
    vy
    weq
    @50
    @5
    c1
    cmin
    @51
    oveq1d
    cnmpt21
    wph
    cG
    cH
    @52
    co
    @10
    cM
    wph
    cG
    cH
    cJ
    cK
    cX
    htpycc.2
    htpycc.5
    htpycc.6
    htpycn
    htpycc.8
    sseldd
    cnmpt22f
    cnmpt2pc
    cnmptcom
    syl5eqel
    @32
    @27
    cc0
    cN
    co
    #
    @34
    @35
    @32
    @31
    cc0
    @0
    wcel
    @57
    @34
    wceq
    wph
    @31
    simpr
    #
    0elunit
    vx
    vy
    @27
    cc0
    cX
    @0
    @9
    @34
    cN
    vx
    vs
    weq
    #
    @1
    cc0
    wceq
    #
    wa
    #
    @9
    @6
    @34
    @61
    @3
    @6
    @8
    @61
    @1
    cc0
    @2
    cle
    @59
    @60
    simpr
    #
    @20
    syl6eqbr
    iftrued
    @61
    @4
    @27
    @5
    cc0
    cL
    @59
    @60
    simpl
    @61
    @5
    c2
    cc0
    cmul
    co
    cc0
    @61
    @1
    cc0
    c2
    cmul
    @62
    oveq2d
    2t0e0
    syl6eq
    oveq12d
    eqtrd
    htpycc.1
    @27
    cc0
    cL
    ovex
    ovmpt2a
    sylancl
    @32
    @36
    @37
    @38
    simpld
    eqtrd
    @32
    @27
    c1
    cN
    co
    #
    @40
    @41
    @32
    @31
    c1
    @0
    wcel
    @63
    @40
    wceq
    @58
    1elunit
    vx
    vy
    @27
    c1
    cX
    @0
    @9
    @40
    cN
    @59
    @1
    c1
    wceq
    #
    wa
    #
    @9
    @8
    @40
    @65
    @3
    @6
    @8
    @65
    @3
    c1
    @2
    cle
    wbr
    #
    @2
    c1
    clt
    wbr
    @66
    wn
    halflt1
    @2
    c1
    halfre
    1re
    ltnlei
    mpbi
    @65
    @1
    c1
    @2
    cle
    @59
    @64
    simpr
    #
    breq1d
    mtbiri
    iffalsed
    @65
    @4
    @27
    @7
    c1
    cM
    @59
    @64
    simpl
    @65
    @7
    c2
    c1
    cmin
    co
    c1
    @65
    @5
    c2
    c1
    cmin
    @65
    @5
    c2
    c1
    cmul
    co
    c2
    @65
    @1
    c1
    c2
    cmul
    @67
    oveq2d
    2t1e2
    syl6eq
    oveq1d
    2m1e1
    syl6eq
    oveq12d
    eqtrd
    htpycc.1
    @27
    c1
    cM
    ovex
    ovmpt2a
    sylancl
    @32
    @39
    @42
    @43
    simprd
    eqtrd
    ishtpyd
end
