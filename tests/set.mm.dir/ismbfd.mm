include "cmbf.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "co.mm"
include "wceq.mm"
include "cxr.mm"
include "wrex.mm"
include "cxp.mm"
include "cr.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "wa.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cin.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "simprl.mm"
include "pnfxr.mm"
include "a1i.mm"
include "mnfxr.mm"
include "simprr.mm"
include "iooin.mm"
include "syl22anc.mm"
include "mnfle.mm"
include "xrleid.mm"
include "breq1.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "ad2antrl.mm"
include "xrmax1.mm"
include "sylancl.mm"
include "ifcl.mm"
include "sylancr.mm"
include "xrletri3.mm"
include "mpbir2and.mm"
include "xrmin2.mm"
include "pnfge.mm"
include "breq2.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "imaeq2d.mm"
include "wfun.mm"
include "adantr.mm"
include "ffun.mm"
include "syl.mm"
include "inpreima.mm"
include "eqtr3d.mm"
include "adantrr.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantrl.mm"
include "inmbl.mm"
include "eqeltrd.mm"
include "imaeq2.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ismbf.mm"
include "mpbird.mm"

theorem ismbfd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume ismbfd.1: |- ( ph -> F : A --> RR )
  assume ismbfd.2: |- ( ( ph /\ x e. RR* ) -> ( `' F " ( x (,) +oo ) ) e. dom vol )
  assume ismbfd.3: |- ( ( ph /\ x e. RR* ) -> ( `' F " ( -oo (,) x ) ) e. dom vol )

  disjoint F x
  disjoint ph x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint ph y
  disjoint ph z
  disjoint A z
  assert |- ( ph -> F e. MblFn )

  proof
    wph
    cF
    cmbf
    wcel
    #
    cF
    ccnv
    #
    vz
    cv
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    vz
    cioo
    crn
    #
    wral
    #
    wph
    @5
    vz
    @6
    @2
    @6
    wcel
    #
    @2
    vx
    cv
    #
    vy
    cv
    #
    cioo
    co
    #
    wceq
    #
    vy
    cxr
    wrex
    vx
    cxr
    wrex
    #
    wph
    @5
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @14
    wfn
    @8
    @13
    wb
    ioof
    @14
    @15
    cioo
    ffn
    vx
    vy
    cxr
    cxr
    @2
    cioo
    ovelrn
    mp2b
    wph
    @12
    @5
    vx
    vy
    cxr
    cxr
    wph
    @9
    cxr
    wcel
    #
    @10
    cxr
    wcel
    #
    wa
    #
    wa
    #
    @5
    @12
    @1
    @11
    cima
    #
    @4
    wcel
    @19
    @20
    @1
    @9
    cpnf
    cioo
    co
    #
    cima
    #
    @1
    cmnf
    @10
    cioo
    co
    #
    cima
    #
    cin
    #
    @4
    @19
    @1
    @21
    @23
    cin
    #
    cima
    #
    @20
    @25
    @19
    @26
    @11
    @1
    @19
    @26
    @9
    cmnf
    cle
    wbr
    #
    cmnf
    @9
    cif
    #
    cpnf
    @10
    cle
    wbr
    #
    cpnf
    @10
    cif
    #
    cioo
    co
    #
    @11
    @19
    @16
    cpnf
    cxr
    wcel
    #
    cmnf
    cxr
    wcel
    #
    @17
    @26
    @32
    wceq
    wph
    @16
    @17
    simprl
    #
    @33
    @19
    pnfxr
    a1i
    @34
    @19
    mnfxr
    a1i
    wph
    @16
    @17
    simprr
    #
    @9
    cpnf
    cmnf
    @10
    iooin
    syl22anc
    @19
    @29
    @9
    @31
    @10
    cioo
    @19
    @29
    @9
    wceq
    #
    @29
    @9
    cle
    wbr
    #
    @9
    @29
    cle
    wbr
    #
    @16
    @38
    wph
    @17
    @16
    cmnf
    @9
    cle
    wbr
    #
    @9
    @9
    cle
    wbr
    #
    @38
    @9
    mnfle
    @9
    xrleid
    @28
    @40
    @41
    @38
    cmnf
    @9
    cmnf
    @29
    @9
    cle
    breq1
    @9
    @29
    @9
    cle
    breq1
    ifboth
    syl2anc
    ad2antrl
    @19
    @16
    @34
    @39
    @35
    mnfxr
    @9
    cmnf
    xrmax1
    sylancl
    @19
    @29
    cxr
    wcel
    #
    @16
    @37
    @38
    @39
    wa
    wb
    @19
    @34
    @16
    @42
    mnfxr
    @35
    @28
    cmnf
    @9
    cxr
    ifcl
    sylancr
    @35
    @29
    @9
    xrletri3
    syl2anc
    mpbir2and
    @19
    @31
    @10
    wceq
    #
    @31
    @10
    cle
    wbr
    #
    @10
    @31
    cle
    wbr
    #
    @19
    @33
    @17
    @44
    pnfxr
    @36
    cpnf
    @10
    xrmin2
    sylancr
    @17
    @45
    wph
    @16
    @17
    @10
    cpnf
    cle
    wbr
    #
    @10
    @10
    cle
    wbr
    #
    @45
    @10
    pnfge
    @10
    xrleid
    @30
    @46
    @47
    @45
    cpnf
    @10
    cpnf
    @31
    @10
    cle
    breq2
    @10
    @31
    @10
    cle
    breq2
    ifboth
    syl2anc
    ad2antll
    @19
    @31
    cxr
    wcel
    #
    @17
    @43
    @44
    @45
    wa
    wb
    @19
    @33
    @17
    @48
    pnfxr
    @36
    @30
    cpnf
    @10
    cxr
    ifcl
    sylancr
    @36
    @31
    @10
    xrletri3
    syl2anc
    mpbir2and
    oveq12d
    eqtrd
    imaeq2d
    @19
    cF
    wfun
    #
    @27
    @25
    wceq
    @19
    cA
    cr
    cF
    wf
    #
    @49
    wph
    @50
    @18
    ismbfd.1
    adantr
    cA
    cr
    cF
    ffun
    syl
    @21
    @23
    cF
    inpreima
    syl
    eqtr3d
    @19
    @22
    @4
    wcel
    #
    @24
    @4
    wcel
    #
    @25
    @4
    wcel
    wph
    @16
    @51
    @17
    ismbfd.2
    adantrr
    wph
    @17
    @52
    @16
    wph
    @1
    cmnf
    @9
    cioo
    co
    #
    cima
    #
    @4
    wcel
    #
    vx
    cxr
    wral
    @17
    @52
    wph
    @55
    vx
    cxr
    ismbfd.3
    ralrimiva
    @55
    @52
    vx
    @10
    cxr
    @9
    @10
    wceq
    #
    @54
    @24
    @4
    @56
    @53
    @23
    @1
    @9
    @10
    cmnf
    cioo
    oveq2
    imaeq2d
    eleq1d
    rspccva
    sylan
    adantrl
    @22
    @24
    inmbl
    syl2anc
    eqeltrd
    @12
    @3
    @20
    @4
    @2
    @11
    @1
    imaeq2
    eleq1d
    syl5ibrcom
    rexlimdvva
    syl5bi
    ralrimiv
    wph
    @50
    @0
    @7
    wb
    ismbfd.1
    vz
    cA
    cF
    ismbf
    syl
    mpbird
end
