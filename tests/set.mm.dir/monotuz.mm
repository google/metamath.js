include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "csb.mm"
include "cv.mm"
include "csbeq1.mm"
include "cuz.mm"
include "cfv.mm"
include "cr.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "eqsstri.mm"
include "wi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "simpl.mm"
include "adantlrr.mm"
include "simplrl.mm"
include "sseldi.mm"
include "simplrr.mm"
include "simpr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "vex.mm"
include "csbie.mm"
include "syl5eqr.mm"
include "ovex.mm"
include "oveq1.mm"
include "csbeq1d.mm"
include "breq12d.mm"
include "vtoclg.mm"
include "w3a.mm"
include "3ad2ant2.mm"
include "simp2l.mm"
include "cle.mm"
include "zre.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ltled.mm"
include "wb.mm"
include "simp11.mm"
include "simp12.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simp2r.mm"
include "syl6eleq.mm"
include "uztrn.mm"
include "syl6eleqr.mm"
include "peano2uz.mm"
include "syl.mm"
include "vtoclf.mm"
include "lttrd.mm"
include "3exp.mm"
include "a2d.mm"
include "uzind2.mm"
include "syl3anc.mm"
include "mpd.mm"
include "ex.mm"
include "ltord1.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "breqan12d.mm"
include "adantl.mm"
include "bitrd.mm"

theorem monotuz
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume monotuz.1: |- ( ( ph /\ y e. H ) -> F < G )
  assume monotuz.2: |- ( ( ph /\ x e. H ) -> C e. RR )
  assume monotuz.3: |- H = ( ZZ>= ` I )
  assume monotuz.4: |- ( x = ( y + 1 ) -> C = G )
  assume monotuz.5: |- ( x = y -> C = F )
  assume monotuz.6: |- ( x = A -> C = D )
  assume monotuz.7: |- ( x = B -> C = E )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint H y
  disjoint ph x
  disjoint ph y
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c y
  disjoint d y
  disjoint D a
  disjoint E a
  disjoint F b
  disjoint G b
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint c x
  disjoint d x
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  assert |- ( ( ph /\ ( A e. H /\ B e. H ) ) -> ( A < B <-> D < E ) )

  proof
    wph
    cA
    cH
    wcel
    #
    cB
    cH
    wcel
    #
    wa
    #
    wa
    cA
    cB
    clt
    wbr
    vx
    cA
    cC
    csb
    #
    vx
    cB
    cC
    csb
    #
    clt
    wbr
    #
    cD
    cE
    clt
    wbr
    #
    wph
    va
    vb
    vx
    va
    cv
    #
    cC
    csb
    #
    vx
    vb
    cv
    #
    cC
    csb
    #
    cA
    cB
    cH
    @3
    @4
    vx
    @7
    @9
    cC
    csbeq1
    vx
    @7
    cA
    cC
    csbeq1
    vx
    @7
    cB
    cC
    csbeq1
    cH
    cI
    cuz
    cfv
    #
    cr
    monotuz.3
    @11
    cz
    cr
    cI
    uzssz
    #
    zssre
    sstri
    eqsstri
    wph
    vx
    cv
    #
    cH
    wcel
    #
    wa
    #
    cC
    cr
    wcel
    #
    wi
    #
    wph
    @7
    cH
    wcel
    #
    wa
    #
    @8
    cr
    wcel
    #
    wi
    vx
    va
    @19
    @20
    vx
    @19
    vx
    nfv
    vx
    @8
    cr
    vx
    @7
    cC
    nfcsb1v
    nfel1
    nfim
    vx
    va
    weq
    #
    @15
    @19
    @16
    @20
    @21
    @14
    @18
    wph
    @13
    @7
    cH
    eleq1
    anbi2d
    @21
    cC
    @8
    cr
    vx
    @7
    cC
    csbeq1a
    eleq1d
    imbi12d
    monotuz.2
    chvar
    #
    wph
    @18
    @9
    cH
    wcel
    #
    wa
    wa
    #
    @7
    @9
    clt
    wbr
    #
    @8
    @10
    clt
    wbr
    #
    @24
    @25
    wa
    #
    @19
    @26
    wph
    @18
    @25
    @19
    @23
    @19
    @25
    simpl
    adantlrr
    @27
    @7
    cz
    wcel
    #
    @9
    cz
    wcel
    @25
    @19
    @26
    wi
    #
    @27
    cH
    cz
    @7
    cH
    @11
    cz
    monotuz.3
    @12
    eqsstri
    #
    wph
    @18
    @23
    @25
    simplrl
    sseldi
    @27
    cH
    cz
    @9
    @30
    wph
    @18
    @23
    @25
    simplrr
    sseldi
    @24
    @25
    simpr
    @19
    @8
    vx
    vc
    cv
    #
    cC
    csb
    #
    clt
    wbr
    #
    wi
    @19
    @8
    vx
    @7
    c1
    caddc
    co
    #
    cC
    csb
    #
    clt
    wbr
    #
    wi
    #
    @19
    @8
    vx
    vd
    cv
    #
    cC
    csb
    #
    clt
    wbr
    #
    wi
    @19
    @8
    vx
    @38
    c1
    caddc
    co
    #
    cC
    csb
    #
    clt
    wbr
    #
    wi
    @29
    vc
    vd
    @7
    @9
    @31
    @34
    wceq
    #
    @33
    @36
    @19
    @44
    @32
    @35
    @8
    clt
    vx
    @31
    @34
    cC
    csbeq1
    breq2d
    imbi2d
    vc
    vd
    weq
    #
    @33
    @40
    @19
    @45
    @32
    @39
    @8
    clt
    vx
    @31
    @38
    cC
    csbeq1
    breq2d
    imbi2d
    @31
    @41
    wceq
    #
    @33
    @43
    @19
    @46
    @32
    @42
    @8
    clt
    vx
    @31
    @41
    cC
    csbeq1
    breq2d
    imbi2d
    vc
    vb
    weq
    #
    @33
    @26
    @19
    @47
    @32
    @10
    @8
    clt
    vx
    @31
    @9
    cC
    csbeq1
    breq2d
    imbi2d
    wph
    vy
    cv
    #
    cH
    wcel
    #
    wa
    #
    cF
    cG
    clt
    wbr
    #
    wi
    #
    @37
    vy
    @7
    cz
    vy
    va
    weq
    #
    @50
    @19
    @51
    @36
    @53
    @49
    @18
    wph
    @48
    @7
    cH
    eleq1
    anbi2d
    @53
    cF
    @8
    cG
    @35
    clt
    @53
    cF
    vx
    @48
    cC
    csb
    #
    @8
    vx
    @48
    cC
    cF
    vy
    vex
    monotuz.5
    csbie
    #
    vx
    @48
    @7
    cC
    csbeq1
    syl5eqr
    @53
    cG
    vx
    @48
    c1
    caddc
    co
    #
    cC
    csb
    #
    @35
    vx
    @56
    cC
    cG
    @48
    c1
    caddc
    ovex
    monotuz.4
    csbie
    #
    @53
    vx
    @56
    @34
    cC
    @48
    @7
    c1
    caddc
    oveq1
    csbeq1d
    syl5eqr
    breq12d
    imbi12d
    monotuz.1
    vtoclg
    @28
    @38
    cz
    wcel
    #
    @7
    @38
    clt
    wbr
    #
    w3a
    #
    @19
    @40
    @43
    @61
    @19
    @40
    @43
    @61
    @19
    @40
    w3a
    #
    @8
    @39
    @42
    @19
    @61
    @20
    @40
    @22
    3ad2ant2
    @62
    wph
    @38
    cH
    wcel
    #
    @39
    cr
    wcel
    #
    @61
    wph
    @18
    @40
    simp2l
    #
    @62
    @38
    @11
    cH
    @62
    @38
    @7
    cuz
    cfv
    wcel
    #
    @7
    @11
    wcel
    @38
    @11
    wcel
    #
    @62
    @66
    @7
    @38
    cle
    wbr
    #
    @61
    @19
    @68
    @40
    @61
    @7
    @38
    @28
    @59
    @7
    cr
    wcel
    @60
    @7
    zre
    3ad2ant1
    @59
    @28
    @38
    cr
    wcel
    @60
    @38
    zre
    3ad2ant2
    @28
    @59
    @60
    simp3
    ltled
    3ad2ant1
    @62
    @28
    @59
    @66
    @68
    wb
    @28
    @59
    @60
    @19
    @40
    simp11
    @28
    @59
    @60
    @19
    @40
    simp12
    @7
    @38
    eluz
    syl2anc
    mpbird
    @62
    @7
    cH
    @11
    @61
    wph
    @18
    @40
    simp2r
    monotuz.3
    syl6eleq
    @7
    @38
    cI
    uztrn
    syl2anc
    #
    monotuz.3
    syl6eleqr
    #
    @17
    wph
    @63
    wa
    #
    @64
    wi
    vx
    vd
    @71
    @64
    vx
    @71
    vx
    nfv
    vx
    @39
    cr
    vx
    @38
    cC
    nfcsb1v
    nfel1
    nfim
    vx
    vd
    weq
    #
    @15
    @71
    @16
    @64
    @72
    @14
    @63
    wph
    @13
    @38
    cH
    eleq1
    anbi2d
    @72
    cC
    @39
    cr
    vx
    @38
    cC
    csbeq1a
    eleq1d
    imbi12d
    monotuz.2
    chvar
    syl2anc
    @62
    wph
    @41
    cH
    wcel
    #
    @42
    cr
    wcel
    #
    @65
    @62
    @41
    @11
    cH
    @62
    @67
    @41
    @11
    wcel
    @69
    cI
    @38
    peano2uz
    syl
    monotuz.3
    syl6eleqr
    @17
    wph
    @73
    wa
    #
    @74
    wi
    vx
    @41
    @75
    @74
    vx
    @75
    vx
    nfv
    vx
    @42
    cr
    vx
    @41
    cC
    nfcsb1v
    nfel1
    nfim
    @38
    c1
    caddc
    ovex
    @13
    @41
    wceq
    #
    @15
    @75
    @16
    @74
    @76
    @14
    @73
    wph
    @13
    @41
    cH
    eleq1
    anbi2d
    @76
    cC
    @42
    cr
    vx
    @41
    cC
    csbeq1a
    eleq1d
    imbi12d
    monotuz.2
    vtoclf
    syl2anc
    @61
    @19
    @40
    simp3
    @62
    wph
    @63
    @39
    @42
    clt
    wbr
    #
    @65
    @70
    @52
    @71
    @77
    wi
    #
    vy
    vd
    @78
    vy
    nfv
    vy
    vd
    weq
    #
    @50
    @71
    @51
    @77
    @79
    @49
    @63
    wph
    @48
    @38
    cH
    eleq1
    anbi2d
    @79
    cF
    @39
    cG
    @42
    clt
    @79
    cF
    @54
    @39
    @55
    vx
    @48
    @38
    cC
    csbeq1
    syl5eqr
    @79
    cG
    @57
    @42
    @58
    @79
    vx
    @56
    @41
    cC
    @48
    @38
    c1
    caddc
    oveq1
    csbeq1d
    syl5eqr
    breq12d
    imbi12d
    monotuz.1
    chvar
    syl2anc
    lttrd
    3exp
    a2d
    uzind2
    syl3anc
    mpd
    ex
    ltord1
    @2
    @5
    @6
    wb
    wph
    @0
    @1
    @3
    cD
    @4
    cE
    clt
    vx
    cA
    cC
    cD
    cH
    @0
    vx
    cD
    nfcvd
    monotuz.6
    csbiegf
    vx
    cB
    cC
    cE
    cH
    @1
    vx
    cE
    nfcvd
    monotuz.7
    csbiegf
    breqan12d
    adantl
    bitrd
end
