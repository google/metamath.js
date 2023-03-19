include "cpco.mm"
include "cfv.mm"
include "co.mm"
include "cphtpc.mm"
include "wbr.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "wer.mm"
include "phtpcer.mm"
include "a1i.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wcel.mm"
include "w3a.mm"
include "pcorevcl.mm"
include "syl.mm"
include "simp2d.mm"
include "eqtr4d.mm"
include "simp1d.mm"
include "pco0.mm"
include "adantr.mm"
include "erref.mm"
include "eqid.mm"
include "pcorev.mm"
include "pcohtpy.mm"
include "pcopt2.mm"
include "syl2anc.mm"
include "ertrd.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "c4.mm"
include "cmul.mm"
include "caddc.mm"
include "cif.mm"
include "cmpt.mm"
include "simp3d.mm"
include "pcoass.mm"
include "pco1.mm"
include "eqtrd.mm"
include "simpr.mm"
include "ertr3d.mm"
include "eqcomd.mm"
include "pcopt.mm"
include "pcorev2.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "syl5eq.mm"
include "breqtrrd.mm"
include "impbida.mm"

theorem pcophtb
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vy: setvar y
  assume pcophtb.h: |- H = ( x e. ( 0 [,] 1 ) |-> ( G ` ( 1 - x ) ) )
  assume pcophtb.p: |- P = ( ( 0 [,] 1 ) X. { ( F ` 0 ) } )
  assume pcophtb.f: |- ( ph -> F e. ( II Cn J ) )
  assume pcophtb.g: |- ( ph -> G e. ( II Cn J ) )
  assume pcophtb.0: |- ( ph -> ( F ` 0 ) = ( G ` 0 ) )
  assume pcophtb.1: |- ( ph -> ( F ` 1 ) = ( G ` 1 ) )

  disjoint G x
  disjoint J x
  disjoint F y
  disjoint x y
  disjoint G y
  disjoint H y
  disjoint J y
  disjoint P y
  disjoint ph y
  assert |- ( ph -> ( ( F ( *p ` J ) H ) ( ~=ph ` J ) P <-> F ( ~=ph ` J ) G ) )

  proof
    wph
    cF
    cH
    cJ
    cpco
    cfv
    #
    co
    #
    cP
    cJ
    cphtpc
    cfv
    #
    wbr
    #
    cF
    cG
    @2
    wbr
    #
    wph
    @3
    wa
    #
    cF
    cF
    cH
    cG
    @0
    co
    #
    @0
    co
    #
    cG
    @2
    cii
    cJ
    ccn
    co
    #
    @8
    @2
    wer
    #
    @5
    cJ
    phtpcer
    #
    a1i
    #
    @5
    @7
    cF
    cc0
    c1
    cicc
    co
    #
    c1
    cG
    cfv
    #
    csn
    cxp
    #
    @0
    co
    #
    cF
    @2
    @8
    @11
    @5
    cF
    @6
    cF
    cJ
    @14
    wph
    c1
    cF
    cfv
    #
    cc0
    @6
    cfv
    #
    wceq
    @3
    wph
    @16
    cc0
    cH
    cfv
    #
    @17
    wph
    @16
    @13
    @18
    pcophtb.1
    wph
    cH
    @8
    wcel
    #
    @18
    @13
    wceq
    #
    c1
    cH
    cfv
    #
    cc0
    cG
    cfv
    #
    wceq
    #
    wph
    cG
    @8
    wcel
    #
    @19
    @20
    @23
    w3a
    pcophtb.g
    vx
    cG
    cH
    cJ
    pcophtb.h
    pcorevcl
    syl
    #
    simp2d
    eqtr4d
    #
    wph
    cH
    cG
    cJ
    wph
    @19
    @20
    @23
    @25
    simp1d
    #
    pcophtb.g
    pco0
    eqtr4d
    adantr
    @5
    cF
    @2
    @8
    @11
    wph
    cF
    @8
    wcel
    #
    @3
    pcophtb.f
    adantr
    #
    erref
    wph
    @6
    @14
    @2
    wbr
    #
    @3
    wph
    @24
    @30
    pcophtb.g
    vx
    @14
    cG
    cH
    cJ
    pcophtb.h
    @14
    eqid
    #
    pcorev
    syl
    adantr
    pcohtpy
    @5
    @28
    @16
    @13
    wceq
    #
    @15
    cF
    @2
    wbr
    @29
    wph
    @32
    @3
    pcophtb.1
    adantr
    @14
    cF
    cJ
    @13
    @31
    pcopt2
    syl2anc
    ertrd
    @5
    @7
    cP
    cG
    @0
    co
    #
    cG
    @2
    @8
    @11
    @5
    @7
    @1
    cG
    @0
    co
    @33
    @2
    @8
    @11
    @5
    vy
    vy
    @12
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
    @34
    c1
    c4
    cdiv
    co
    #
    cle
    wbr
    c2
    @34
    cmul
    co
    @34
    @36
    caddc
    co
    cif
    @34
    c2
    cdiv
    co
    @35
    caddc
    co
    cif
    cmpt
    #
    cF
    cH
    cG
    cJ
    @29
    wph
    @19
    @3
    @27
    adantr
    wph
    @24
    @3
    pcophtb.g
    adantr
    #
    wph
    @16
    @18
    wceq
    #
    @3
    @26
    adantr
    wph
    @23
    @3
    wph
    @19
    @20
    @23
    @25
    simp3d
    #
    adantr
    @37
    eqid
    pcoass
    @5
    @1
    cG
    cP
    cJ
    cG
    wph
    c1
    @1
    cfv
    #
    @22
    wceq
    @3
    wph
    @41
    @21
    @22
    wph
    cF
    cH
    cJ
    pcophtb.f
    @27
    pco1
    @40
    eqtrd
    adantr
    wph
    @3
    simpr
    @5
    cG
    @2
    @8
    @11
    @38
    erref
    pcohtpy
    ertr3d
    @5
    @24
    @22
    cc0
    cF
    cfv
    #
    wceq
    @33
    cG
    @2
    wbr
    @38
    @5
    @42
    @22
    wph
    @42
    @22
    wceq
    @3
    pcophtb.0
    adantr
    eqcomd
    cP
    cG
    cJ
    @42
    pcophtb.p
    pcopt
    syl2anc
    ertrd
    ertr3d
    wph
    @4
    wa
    #
    @1
    cG
    cH
    @0
    co
    #
    cP
    @2
    @8
    @9
    @43
    @10
    a1i
    #
    @43
    cF
    cH
    cG
    cJ
    cH
    wph
    @39
    @4
    @26
    adantr
    wph
    @4
    simpr
    @43
    cH
    @2
    @8
    @45
    wph
    @19
    @4
    @27
    adantr
    erref
    pcohtpy
    wph
    @44
    cP
    @2
    wbr
    @4
    wph
    @44
    @12
    @22
    csn
    #
    cxp
    #
    cP
    @2
    wph
    @24
    @44
    @47
    @2
    wbr
    pcophtb.g
    vx
    @47
    cG
    cH
    cJ
    pcophtb.h
    @47
    eqid
    pcorev2
    syl
    wph
    cP
    @12
    @42
    csn
    #
    cxp
    @47
    pcophtb.p
    wph
    @48
    @46
    @12
    wph
    @42
    @22
    pcophtb.0
    sneqd
    xpeq2d
    syl5eq
    breqtrrd
    adantr
    ertrd
    impbida
end
