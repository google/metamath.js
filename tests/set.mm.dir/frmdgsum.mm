include "cword.mm"
include "wcel.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "cs1.mm"
include "cconcat.mm"
include "coeq2.mm"
include "co02.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "frmd0.mm"
include "gsum0.mm"
include "a1i.mm"
include "wa.mm"
include "oveq1.mm"
include "wf.mm"
include "simprl.mm"
include "simprr.mm"
include "s1cld.mm"
include "vrmdf.mm"
include "adantr.mm"
include "ccatco.mm"
include "syl3anc.mm"
include "cfv.mm"
include "s1co.mm"
include "syl2anc.mm"
include "vrmdval.mm"
include "adantrl.mm"
include "s1eqd.mm"
include "eqtrd.mm"
include "cplusg.mm"
include "cmnd.mm"
include "cbs.mm"
include "frmdmnd.mm"
include "wrdco.mm"
include "eqid.mm"
include "frmdbas.mm"
include "wrdeq.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "gsumccat.mm"
include "gsumws1.mm"
include "gsumwcl.mm"
include "frmdadd.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "wrdind.mm"
include "impcom.mm"

theorem frmdgsum
  let cU: class U
  let cI: class I
  let cM: class M
  let cV: class V
  let cW: class W
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  assume frmdmnd.m: |- M = ( freeMnd ` I )
  assume frmdgsum.u: |- U = ( varFMnd ` I )


  assert |- ( ( I e. V /\ W e. Word I ) -> ( M gsum ( U o. W ) ) = W )

  proof
    cW
    cI
    cword
    #
    wcel
    cI
    cV
    wcel
    #
    cM
    cU
    cW
    ccom
    #
    cgsu
    co
    #
    cW
    wceq
    #
    @1
    cM
    cU
    vx
    cv
    #
    ccom
    #
    cgsu
    co
    #
    @5
    wceq
    #
    wi
    @1
    cM
    c0
    cgsu
    co
    #
    c0
    wceq
    #
    wi
    @1
    cM
    cU
    vy
    cv
    #
    ccom
    #
    cgsu
    co
    #
    @11
    wceq
    #
    wi
    @1
    cM
    cU
    @11
    vz
    cv
    #
    cs1
    #
    cconcat
    co
    #
    ccom
    #
    cgsu
    co
    #
    @17
    wceq
    #
    wi
    @1
    @4
    wi
    vx
    vy
    vz
    cW
    cI
    @5
    c0
    wceq
    #
    @8
    @10
    @1
    @21
    @7
    @9
    @5
    c0
    @21
    @6
    c0
    cM
    cgsu
    @21
    @6
    cU
    c0
    ccom
    c0
    @5
    c0
    cU
    coeq2
    cU
    co02
    syl6eq
    oveq2d
    @21
    id
    eqeq12d
    imbi2d
    @5
    @11
    wceq
    #
    @8
    @14
    @1
    @22
    @7
    @13
    @5
    @11
    @22
    @6
    @12
    cM
    cgsu
    @5
    @11
    cU
    coeq2
    oveq2d
    @22
    id
    eqeq12d
    imbi2d
    @5
    @17
    wceq
    #
    @8
    @20
    @1
    @23
    @7
    @19
    @5
    @17
    @23
    @6
    @18
    cM
    cgsu
    @5
    @17
    cU
    coeq2
    oveq2d
    @23
    id
    eqeq12d
    imbi2d
    @5
    cW
    wceq
    #
    @8
    @4
    @1
    @24
    @7
    @3
    @5
    cW
    @24
    @6
    @2
    cM
    cgsu
    @5
    cW
    cU
    coeq2
    oveq2d
    @24
    id
    eqeq12d
    imbi2d
    @10
    @1
    cM
    c0
    cI
    cM
    frmdmnd.m
    frmd0
    gsum0
    a1i
    @11
    @0
    wcel
    #
    @15
    cI
    wcel
    #
    wa
    #
    @1
    @14
    @20
    @1
    @27
    @14
    @20
    wi
    @14
    @20
    @1
    @27
    wa
    #
    @13
    @16
    cconcat
    co
    #
    @17
    wceq
    @13
    @11
    @16
    cconcat
    oveq1
    @28
    @19
    @29
    @17
    @28
    @19
    cM
    @12
    @16
    cs1
    #
    cconcat
    co
    #
    cgsu
    co
    #
    @29
    @28
    @18
    @31
    cM
    cgsu
    @28
    @18
    @12
    cU
    @16
    ccom
    #
    cconcat
    co
    #
    @31
    @28
    @25
    @16
    @0
    wcel
    cI
    @0
    cU
    wf
    #
    @18
    @34
    wceq
    @1
    @25
    @26
    simprl
    #
    @28
    @15
    cI
    @1
    @25
    @26
    simprr
    #
    s1cld
    #
    @1
    @35
    @27
    cU
    cI
    cV
    frmdgsum.u
    vrmdf
    adantr
    #
    cI
    @0
    @11
    @16
    cU
    ccatco
    syl3anc
    @28
    @33
    @30
    @12
    cconcat
    @28
    @33
    @15
    cU
    cfv
    #
    cs1
    #
    @30
    @28
    @26
    @35
    @33
    @41
    wceq
    @37
    @39
    cI
    @0
    @15
    cU
    s1co
    syl2anc
    @28
    @40
    @16
    @1
    @26
    @40
    @16
    wceq
    @25
    @15
    cU
    cI
    cV
    frmdgsum.u
    vrmdval
    adantrl
    s1eqd
    eqtrd
    oveq2d
    eqtrd
    oveq2d
    @28
    @32
    @13
    cM
    @30
    cgsu
    co
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @29
    @28
    cM
    cmnd
    wcel
    #
    @12
    cM
    cbs
    cfv
    #
    cword
    #
    wcel
    #
    @30
    @47
    wcel
    @32
    @44
    wceq
    @1
    @45
    @27
    cI
    cM
    cV
    frmdmnd.m
    frmdmnd
    adantr
    #
    @28
    @12
    @0
    cword
    #
    @47
    @28
    @25
    @35
    @12
    @50
    wcel
    @36
    @39
    cI
    @0
    cU
    @11
    wrdco
    syl2anc
    @28
    @46
    @0
    wceq
    #
    @47
    @50
    wceq
    @1
    @51
    @27
    @46
    cI
    cM
    cV
    frmdmnd.m
    @46
    eqid
    #
    frmdbas
    adantr
    #
    @46
    @0
    wrdeq
    syl
    eleqtrrd
    #
    @28
    @16
    @46
    @28
    @16
    @0
    @46
    @38
    @53
    eleqtrrd
    #
    s1cld
    @46
    @43
    cM
    @12
    @30
    @52
    @43
    eqid
    #
    gsumccat
    syl3anc
    @28
    @44
    @13
    @16
    @43
    co
    #
    @29
    @28
    @42
    @16
    @13
    @43
    @28
    @16
    @46
    wcel
    #
    @42
    @16
    wceq
    @55
    @46
    @16
    cM
    @52
    gsumws1
    syl
    oveq2d
    @28
    @13
    @46
    wcel
    #
    @58
    @57
    @29
    wceq
    @28
    @45
    @48
    @59
    @49
    @54
    @46
    cM
    @12
    @52
    gsumwcl
    syl2anc
    @55
    @46
    @43
    cI
    cM
    @13
    @16
    frmdmnd.m
    @52
    @56
    frmdadd
    syl2anc
    eqtrd
    eqtrd
    eqtrd
    eqeq1d
    syl5ibr
    expcom
    a2d
    wrdind
    impcom
end
