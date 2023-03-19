include "cpco.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cii.mm"
include "ccn.mm"
include "pcoval.mm"
include "ctopon.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnmptid.mm"
include "0elunit.mm"
include "cnmptc.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "eqid.mm"
include "dfii2.mm"
include "cr.mm"
include "0re.mm"
include "1re.mm"
include "halfre.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "halflt1.mm"
include "elicc2i.mm"
include "mpbir3an.mm"
include "wceq.mm"
include "wa.mm"
include "adantr.mm"
include "simprl.mm"
include "oveq2d.mm"
include "2cn.mm"
include "2ne0.mm"
include "recidi.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "1m1e0.mm"
include "3eqtr4d.mm"
include "wss.mm"
include "retopon.mm"
include "iccssre.mm"
include "mp2an.mm"
include "resttopon.mm"
include "cnmpt1st.mm"
include "iihalf1cn.mm"
include "oveq2.mm"
include "cnmpt21.mm"
include "cnmpt21f.mm"
include "iihalf2cn.mm"
include "cnmpt2pc.mm"
include "breq1.mm"
include "ifbieq12d.mm"
include "cnmpt12.mm"
include "eqeltrd.mm"

theorem pcocn
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cX: class X
  let cH: class H
  let vj: setvar j
  assume pcoval.2: |- ( ph -> F e. ( II Cn J ) )
  assume pcoval.3: |- ( ph -> G e. ( II Cn J ) )
  assume pcoval2.4: |- ( ph -> ( F ` 1 ) = ( G ` 0 ) )


  assert |- ( ph -> ( F ( *p ` J ) G ) e. ( II Cn J ) )

  proof
    wph
    cF
    cG
    cJ
    cpco
    cfv
    co
    vx
    cc0
    c1
    cicc
    co
    #
    vx
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
    c2
    @1
    cmul
    co
    #
    cF
    cfv
    #
    @4
    c1
    cmin
    co
    #
    cG
    cfv
    #
    cif
    #
    cmpt
    cii
    cJ
    ccn
    co
    wph
    vx
    cF
    cG
    cJ
    pcoval.2
    pcoval.3
    pcoval
    wph
    vx
    vy
    vz
    @1
    cc0
    vy
    cv
    #
    @2
    cle
    wbr
    #
    c2
    @9
    cmul
    co
    #
    cF
    cfv
    #
    @11
    c1
    cmin
    co
    #
    cG
    cfv
    #
    cif
    #
    @8
    cii
    cii
    cii
    cJ
    @0
    @0
    @0
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    wph
    vx
    cii
    @0
    @16
    cnmptid
    wph
    vx
    cc0
    cii
    cii
    @0
    @0
    @16
    @16
    cc0
    @0
    wcel
    wph
    0elunit
    a1i
    cnmptc
    @16
    @16
    wph
    vy
    vz
    cc0
    @2
    c1
    @12
    cioo
    crn
    ctg
    cfv
    #
    @14
    cii
    cJ
    @17
    cc0
    @2
    cicc
    co
    #
    crest
    co
    #
    @17
    @2
    c1
    cicc
    co
    #
    crest
    co
    #
    cii
    @0
    @17
    eqid
    @19
    eqid
    #
    @21
    eqid
    #
    dfii2
    cc0
    cr
    wcel
    #
    wph
    0re
    a1i
    c1
    cr
    wcel
    #
    wph
    1re
    a1i
    @2
    @0
    wcel
    #
    wph
    @26
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
    @16
    wph
    @9
    @2
    wceq
    #
    vz
    cv
    #
    @0
    wcel
    #
    wa
    #
    wa
    #
    c1
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    @12
    @14
    wph
    @33
    @34
    wceq
    @31
    pcoval2.4
    adantr
    @32
    @11
    c1
    cF
    @32
    @11
    c2
    @2
    cmul
    co
    c1
    @32
    @9
    @2
    c2
    cmul
    wph
    @28
    @30
    simprl
    oveq2d
    c2
    2cn
    2ne0
    recidi
    syl6eq
    #
    fveq2d
    @32
    @13
    cc0
    cG
    @32
    @13
    c1
    c1
    cmin
    co
    cc0
    @32
    @11
    c1
    c1
    cmin
    @35
    oveq1d
    1m1e0
    syl6eq
    fveq2d
    3eqtr4d
    wph
    vy
    vz
    @11
    cF
    @19
    cii
    cii
    cJ
    @18
    @0
    @19
    @18
    ctopon
    cfv
    wcel
    #
    wph
    @17
    cr
    ctopon
    cfv
    wcel
    #
    @18
    cr
    wss
    #
    @36
    retopon
    @24
    @27
    @38
    0re
    halfre
    cc0
    @2
    iccssre
    mp2an
    @18
    @17
    cr
    resttopon
    mp2an
    a1i
    #
    @16
    wph
    vy
    vz
    vx
    @9
    @4
    @11
    @19
    cii
    @19
    cii
    @18
    @0
    @18
    @39
    @16
    wph
    vy
    vz
    @19
    cii
    @18
    @0
    @39
    @16
    cnmpt1st
    @39
    vx
    @18
    @4
    cmpt
    @19
    cii
    ccn
    co
    wcel
    wph
    vx
    @19
    @22
    iihalf1cn
    a1i
    @1
    @9
    c2
    cmul
    oveq2
    #
    cnmpt21
    pcoval.2
    cnmpt21f
    wph
    vy
    vz
    @13
    cG
    @21
    cii
    cii
    cJ
    @20
    @0
    @21
    @20
    ctopon
    cfv
    wcel
    #
    wph
    @37
    @20
    cr
    wss
    #
    @41
    retopon
    @27
    @25
    @42
    halfre
    1re
    @2
    c1
    iccssre
    mp2an
    @20
    @17
    cr
    resttopon
    mp2an
    a1i
    #
    @16
    wph
    vy
    vz
    vx
    @9
    @6
    @13
    @21
    cii
    @21
    cii
    @20
    @0
    @20
    @43
    @16
    wph
    vy
    vz
    @21
    cii
    @20
    @0
    @43
    @16
    cnmpt1st
    @43
    vx
    @20
    @6
    cmpt
    @21
    cii
    ccn
    co
    wcel
    wph
    vx
    @21
    @23
    iihalf2cn
    a1i
    @1
    @9
    wceq
    @4
    @11
    c1
    cmin
    @40
    oveq1d
    cnmpt21
    pcoval.3
    cnmpt21f
    cnmpt2pc
    @9
    @1
    wceq
    #
    @15
    @8
    wceq
    @29
    cc0
    wceq
    @44
    @10
    @3
    @12
    @14
    @5
    @7
    @9
    @1
    @2
    cle
    breq1
    @44
    @11
    @4
    cF
    @9
    @1
    c2
    cmul
    oveq2
    #
    fveq2d
    @44
    @13
    @6
    cG
    @44
    @11
    @4
    c1
    cmin
    @45
    oveq1d
    fveq2d
    ifbieq12d
    adantr
    cnmpt12
    eqeltrd
end
