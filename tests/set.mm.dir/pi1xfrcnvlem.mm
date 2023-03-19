include "ccnv.mm"
include "cbs.mm"
include "cfv.mm"
include "cuni.mm"
include "cv.mm"
include "cphtpc.mm"
include "cec.mm"
include "cpco.mm"
include "co.mm"
include "cop.mm"
include "cmpt.mm"
include "ccom.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvex.mm"
include "ecexg.mm"
include "mp1i.mm"
include "fliftcnv.mm"
include "cii.mm"
include "ccn.mm"
include "cc0.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "pcorevcl.mm"
include "syl.mm"
include "simp1d.mm"
include "adantr.mm"
include "cicc.mm"
include "wf.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "0elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "pi1eluni.mm"
include "biimpa.mm"
include "simp3d.mm"
include "pcocn.mm"
include "simp2d.mm"
include "eqtr4d.mm"
include "pco0.mm"
include "eqtrd.mm"
include "pco1.mm"
include "wb.mm"
include "1elunit.mm"
include "eqidd.mm"
include "mpbir3and.mm"
include "eceq1.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eceq1d.mm"
include "opeq12d.mm"
include "fmptco.mm"
include "wer.mm"
include "phtpcer.mm"
include "eqtr2d.mm"
include "erref.mm"
include "csn.mm"
include "cxp.mm"
include "wbr.mm"
include "eqid.mm"
include "pcopt2.mm"
include "syl2anc.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "c4.mm"
include "cmul.mm"
include "caddc.mm"
include "cif.mm"
include "eqcomd.mm"
include "pcoass.mm"
include "pcorev2.mm"
include "pcohtpy.mm"
include "ertr2d.mm"
include "ertr3d.mm"
include "ertr4d.mm"
include "pcopt.mm"
include "ertrd.mm"
include "erthi.mm"
include "opeq2d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "rncoss.mm"
include "sseqtr4i.mm"
include "syl6eqss.mm"

theorem pi1xfrcnvlem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vs: setvar s
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume pi1xfr.p: |- P = ( J pi1 ( F ` 0 ) )
  assume pi1xfr.q: |- Q = ( J pi1 ( F ` 1 ) )
  assume pi1xfr.b: |- B = ( Base ` P )
  assume pi1xfr.g: |- G = ran ( g e. U. B |-> <. [ g ] ( ~=ph ` J ) , [ ( I ( *p ` J ) ( g ( *p ` J ) F ) ) ] ( ~=ph ` J ) >. )
  assume pi1xfr.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1xfr.f: |- ( ph -> F e. ( II Cn J ) )
  assume pi1xfr.i: |- I = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )
  assume pi1xfrcnv.h: |- H = ran ( h e. U. ( Base ` Q ) |-> <. [ h ] ( ~=ph ` J ) , [ ( F ( *p ` J ) ( h ( *p ` J ) I ) ) ] ( ~=ph ` J ) >. )

  disjoint g h
  disjoint g x
  disjoint B g
  disjoint h x
  disjoint B h
  disjoint B x
  disjoint F g
  disjoint F h
  disjoint F x
  disjoint I g
  disjoint I h
  disjoint I x
  disjoint G h
  disjoint g ph
  disjoint h ph
  disjoint ph x
  disjoint J g
  disjoint J h
  disjoint J x
  disjoint P g
  disjoint P h
  disjoint P x
  disjoint Q g
  disjoint Q h
  disjoint Q x
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g s
  disjoint g u
  disjoint g y
  disjoint g z
  disjoint h s
  disjoint h u
  disjoint h y
  disjoint h z
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F s
  disjoint F u
  disjoint F y
  disjoint F z
  disjoint I s
  disjoint I u
  disjoint I y
  disjoint I z
  disjoint A g
  disjoint A s
  disjoint A x
  disjoint G f
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H s
  disjoint H z
  disjoint f ph
  disjoint ph s
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J s
  disjoint J u
  disjoint J y
  disjoint J z
  disjoint P f
  disjoint P s
  disjoint P y
  disjoint P z
  disjoint Q f
  disjoint Q s
  disjoint Q y
  disjoint Q z
  assert |- ( ph -> `' G C_ H )

  proof
    wph
    cG
    ccnv
    #
    vh
    cQ
    cbs
    cfv
    #
    cuni
    #
    vh
    cv
    #
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cF
    @3
    cI
    cJ
    cpco
    cfv
    #
    co
    #
    @6
    co
    #
    @4
    cec
    #
    cop
    #
    cmpt
    #
    vg
    cB
    cuni
    #
    cI
    vg
    cv
    #
    cF
    @6
    co
    #
    @6
    co
    #
    cmpt
    #
    ccom
    #
    crn
    #
    cH
    wph
    @0
    vg
    @12
    @15
    @4
    cec
    #
    @13
    @4
    cec
    #
    cop
    #
    cmpt
    #
    crn
    @18
    wph
    vg
    @20
    @19
    cvv
    cvv
    cG
    @12
    pi1xfr.g
    @4
    cvv
    wcel
    #
    @20
    cvv
    wcel
    wph
    @13
    @12
    wcel
    #
    wa
    #
    cJ
    cphtpc
    fvex
    #
    @13
    cvv
    @4
    ecexg
    mp1i
    @23
    @19
    cvv
    wcel
    @25
    @26
    @15
    cvv
    @4
    ecexg
    mp1i
    fliftcnv
    wph
    @17
    @22
    wph
    @17
    vg
    @12
    @19
    cF
    @15
    cI
    @6
    co
    #
    @6
    co
    #
    @4
    cec
    #
    cop
    #
    cmpt
    @22
    wph
    vg
    vh
    @12
    @2
    @15
    @10
    @30
    @16
    @11
    @25
    @15
    @2
    wcel
    #
    @15
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cc0
    @15
    cfv
    #
    c1
    cF
    cfv
    #
    wceq
    #
    c1
    @15
    cfv
    #
    @35
    wceq
    #
    @25
    cI
    @14
    cJ
    wph
    cI
    @32
    wcel
    #
    @24
    wph
    @39
    cc0
    cI
    cfv
    #
    @35
    wceq
    #
    c1
    cI
    cfv
    #
    cc0
    cF
    cfv
    #
    wceq
    #
    wph
    cF
    @32
    wcel
    #
    @39
    @41
    @44
    w3a
    pi1xfr.f
    vx
    cF
    cI
    cJ
    pi1xfr.i
    pcorevcl
    syl
    #
    simp1d
    adantr
    #
    @25
    @13
    cF
    cJ
    @25
    @13
    @32
    wcel
    #
    cc0
    @13
    cfv
    #
    @43
    wceq
    #
    c1
    @13
    cfv
    #
    @43
    wceq
    #
    wph
    @24
    @48
    @50
    @52
    w3a
    wph
    cB
    @13
    cP
    cJ
    cX
    @43
    pi1xfr.p
    pi1xfr.j
    wph
    cc0
    c1
    cicc
    co
    #
    cX
    cF
    wf
    #
    cc0
    @53
    wcel
    @43
    cX
    wcel
    wph
    cii
    @53
    ctopon
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    @45
    @54
    @55
    wph
    iitopon
    a1i
    pi1xfr.j
    pi1xfr.f
    cF
    cii
    cJ
    @53
    cX
    cnf2
    syl3anc
    #
    0elunit
    @53
    cX
    cc0
    cF
    ffvelrn
    sylancl
    cB
    cP
    cbs
    cfv
    wceq
    wph
    pi1xfr.b
    a1i
    pi1eluni
    biimpa
    #
    simp1d
    #
    wph
    @45
    @24
    pi1xfr.f
    adantr
    #
    @25
    @48
    @50
    @52
    @57
    simp3d
    #
    pcocn
    #
    @25
    @42
    @49
    cc0
    @14
    cfv
    @25
    @42
    @43
    @49
    wph
    @44
    @24
    wph
    @39
    @41
    @44
    @46
    simp3d
    adantr
    @25
    @48
    @50
    @52
    @57
    simp2d
    #
    eqtr4d
    #
    @25
    @13
    cF
    cJ
    @58
    @59
    pco0
    eqtr4d
    #
    pcocn
    @25
    @34
    @40
    @35
    @25
    cI
    @14
    cJ
    @47
    @61
    pco0
    wph
    @41
    @24
    wph
    @39
    @41
    @44
    @46
    simp2d
    adantr
    #
    eqtrd
    @25
    @37
    c1
    @14
    cfv
    #
    @35
    @25
    cI
    @14
    cJ
    @47
    @61
    pco1
    @25
    @13
    cF
    cJ
    @58
    @59
    pco1
    #
    eqtrd
    wph
    @31
    @33
    @36
    @38
    w3a
    wb
    @24
    wph
    @1
    @15
    cQ
    cJ
    cX
    @35
    pi1xfr.q
    pi1xfr.j
    wph
    @54
    c1
    @53
    wcel
    @35
    cX
    wcel
    @56
    1elunit
    @53
    cX
    c1
    cF
    ffvelrn
    sylancl
    wph
    @1
    eqidd
    pi1eluni
    adantr
    mpbir3and
    wph
    @16
    eqidd
    wph
    @11
    eqidd
    @3
    @15
    wceq
    #
    @5
    @19
    @9
    @29
    @3
    @15
    @4
    eceq1
    @68
    @8
    @28
    @4
    @68
    @7
    @27
    cF
    @6
    @3
    @15
    cI
    @6
    oveq1
    oveq2d
    eceq1d
    opeq12d
    fmptco
    wph
    vg
    @12
    @30
    @21
    @25
    @29
    @20
    @19
    @25
    @28
    @13
    @4
    @32
    @32
    @4
    wer
    @25
    cJ
    phtpcer
    a1i
    #
    @25
    @28
    cF
    cI
    @13
    @6
    co
    #
    @6
    co
    #
    @13
    @4
    @32
    @69
    @25
    cF
    @70
    cF
    cJ
    @27
    @25
    cc0
    @70
    cfv
    @40
    @35
    @25
    cI
    @13
    cJ
    @47
    @58
    pco0
    @65
    eqtr2d
    @25
    cF
    @4
    @32
    @69
    @59
    erref
    @25
    @70
    cI
    @14
    cI
    @6
    co
    #
    @6
    co
    @27
    @4
    @32
    @69
    @25
    cI
    @13
    cI
    cJ
    @72
    @63
    @25
    cI
    @4
    @32
    @69
    @47
    erref
    @25
    @13
    @13
    @53
    @43
    csn
    cxp
    #
    @6
    co
    #
    @72
    @4
    @32
    @69
    @25
    @48
    @52
    @74
    @13
    @4
    wbr
    @58
    @60
    @73
    @13
    cJ
    @43
    @73
    eqid
    #
    pcopt2
    syl2anc
    @25
    @72
    @13
    cF
    cI
    @6
    co
    #
    @6
    co
    @74
    @4
    @32
    @69
    @25
    vx
    vx
    @53
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
    @77
    c1
    c4
    cdiv
    co
    #
    cle
    wbr
    c2
    @77
    cmul
    co
    @77
    @79
    caddc
    co
    cif
    @77
    c2
    cdiv
    co
    @78
    caddc
    co
    cif
    cmpt
    #
    @13
    cF
    cI
    cJ
    @58
    @59
    @47
    @60
    @25
    @40
    @35
    @65
    eqcomd
    #
    @80
    eqid
    #
    pcoass
    @25
    @13
    @76
    @13
    cJ
    @73
    @25
    @51
    @43
    cc0
    @76
    cfv
    @60
    @25
    cF
    cI
    cJ
    @59
    @47
    pco0
    eqtr4d
    @25
    @13
    @4
    @32
    @69
    @58
    erref
    #
    @25
    @45
    @76
    @73
    @4
    wbr
    @59
    vx
    @73
    cF
    cI
    cJ
    pi1xfr.i
    @75
    pcorev2
    syl
    #
    pcohtpy
    ertr2d
    ertr3d
    pcohtpy
    @25
    vx
    @80
    cI
    @14
    cI
    cJ
    @47
    @61
    @47
    @64
    @25
    @66
    @35
    @40
    @67
    @65
    eqtr4d
    @82
    pcoass
    ertr4d
    pcohtpy
    @25
    @71
    @76
    @13
    @6
    co
    #
    @13
    @4
    @32
    @69
    @25
    vx
    @80
    cF
    cI
    @13
    cJ
    @59
    @47
    @58
    @81
    @63
    @82
    pcoass
    @25
    @85
    @73
    @13
    @6
    co
    #
    @13
    @4
    @32
    @69
    @25
    @76
    @13
    @73
    cJ
    @13
    @25
    c1
    @76
    cfv
    @42
    @49
    @25
    cF
    cI
    cJ
    @59
    @47
    pco1
    @63
    eqtrd
    @84
    @83
    pcohtpy
    @25
    @48
    @50
    @86
    @13
    @4
    wbr
    @58
    @62
    @73
    @13
    cJ
    @43
    @75
    pcopt
    syl2anc
    ertrd
    ertr3d
    ertr3d
    erthi
    opeq2d
    mpteq2dva
    eqtrd
    rneqd
    eqtr4d
    @18
    @11
    crn
    cH
    @11
    @16
    rncoss
    pi1xfrcnv.h
    sseqtr4i
    syl6eqss
end
