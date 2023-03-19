include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "cv.mm"
include "wf1.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cfv.mm"
include "wf.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "f1f.mm"
include "syl.mm"
include "cop.mm"
include "wceq.mm"
include "fpr2g.mm"
include "biimpa.mm"
include "simp1d.mm"
include "syl21anc.mm"
include "simp2d.mm"
include "prid1g.mm"
include "prid2g.mm"
include "jca.mm"
include "simpl3.mm"
include "f1veqaeq.mm"
include "necon3d.mm"
include "imp.mm"
include "simprr.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "wss.mm"
include "wf1o.mm"
include "simpll1.mm"
include "simplrl.mm"
include "simpll2.mm"
include "simplrr.mm"
include "simpll3.mm"
include "f1oprg.mm"
include "syl22anc.mm"
include "f1of1.mm"
include "prssi.mm"
include "syl2anc.mm"
include "f1ss.mm"
include "fvpr1g.mm"
include "eqcomd.mm"
include "fvpr2g.mm"
include "prex.mm"
include "f1eq1.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "spcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "simprrl.mm"
include "mpbid.mm"
include "simprrr.mm"
include "eximdv.mm"
include "mpd.mm"
include "rexlimdvva.mm"
include "impbida.mm"

theorem f1prex
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let cV: class V
  let cW: class W
  assume f1prex.1: |- ( x = ( f ` A ) -> ( ps <-> ch ) )
  assume f1prex.2: |- ( y = ( f ` B ) -> ( ch <-> ph ) )

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint D f
  disjoint D x
  disjoint D y
  disjoint V f
  disjoint V x
  disjoint V y
  disjoint W f
  disjoint W x
  disjoint W y
  disjoint ch x
  disjoint f ps
  disjoint ph x
  disjoint ph y
  assert |- ( ( A e. V /\ B e. W /\ A =/= B ) -> ( E. f ( f : { A , B } -1-1-> D /\ ph ) <-> E. x e. D E. y e. D ( x =/= y /\ ps ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    cpr
    #
    cD
    vf
    cv
    #
    wf1
    #
    wph
    wa
    #
    vf
    wex
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    wps
    wa
    #
    vy
    cD
    wrex
    vx
    cD
    wrex
    #
    @3
    @8
    @13
    @3
    @7
    @13
    vf
    @3
    @7
    @13
    @3
    @7
    wa
    #
    cA
    @5
    cfv
    #
    cD
    wcel
    #
    cB
    @5
    cfv
    #
    cD
    wcel
    #
    @15
    @17
    wne
    #
    wph
    wa
    #
    @13
    @14
    @0
    @1
    @4
    cD
    @5
    wf
    #
    @16
    @0
    @1
    @2
    @7
    simpl1
    #
    @0
    @1
    @2
    @7
    simpl2
    #
    @14
    @6
    @21
    @3
    @6
    wph
    simprl
    #
    @4
    cD
    @5
    f1f
    syl
    #
    @0
    @1
    wa
    #
    @21
    wa
    #
    @16
    @18
    @5
    cA
    @15
    cop
    cB
    @17
    cop
    cpr
    wceq
    #
    @26
    @21
    @16
    @18
    @28
    w3a
    cA
    cB
    cD
    @5
    cV
    cW
    fpr2g
    biimpa
    #
    simp1d
    syl21anc
    @14
    @0
    @1
    @21
    @18
    @22
    @23
    @25
    @27
    @16
    @18
    @28
    @29
    simp2d
    syl21anc
    @14
    @19
    wph
    @14
    @6
    cA
    @4
    wcel
    #
    cB
    @4
    wcel
    #
    wa
    #
    @2
    @19
    @24
    @14
    @30
    @31
    @14
    @0
    @30
    @22
    cA
    cB
    cV
    prid1g
    syl
    @14
    @1
    @31
    @23
    cA
    cB
    cW
    prid2g
    syl
    jca
    @0
    @1
    @2
    @7
    simpl3
    @6
    @32
    wa
    #
    @2
    @19
    @33
    @15
    @17
    cA
    cB
    @4
    cD
    cA
    cB
    @5
    f1veqaeq
    necon3d
    imp
    syl21anc
    @3
    @6
    wph
    simprr
    jca
    @12
    @20
    @15
    @10
    wne
    #
    wch
    wa
    vx
    vy
    @15
    @17
    cD
    cD
    @9
    @15
    wceq
    #
    @11
    @34
    wps
    wch
    @9
    @15
    @10
    neeq1
    f1prex.1
    anbi12d
    @10
    @17
    wceq
    #
    @34
    @19
    wch
    wph
    @10
    @17
    @15
    neeq2
    f1prex.2
    anbi12d
    rspc2ev
    syl3anc
    ex
    exlimdv
    imp
    @3
    @13
    @8
    @3
    @12
    @8
    vx
    vy
    cD
    cD
    @3
    @9
    cD
    wcel
    #
    @10
    cD
    wcel
    #
    wa
    #
    wa
    #
    @12
    @8
    @40
    @12
    wa
    #
    @6
    @35
    @36
    wa
    #
    wa
    #
    vf
    wex
    #
    @8
    @41
    @4
    cD
    cA
    @9
    cop
    #
    cB
    @10
    cop
    #
    cpr
    #
    wf1
    #
    @9
    cA
    @47
    cfv
    #
    wceq
    #
    @10
    cB
    @47
    cfv
    #
    wceq
    #
    @44
    @41
    @4
    @9
    @10
    cpr
    #
    @47
    wf1
    #
    @53
    cD
    wss
    #
    @48
    @41
    @4
    @53
    @47
    wf1o
    #
    @54
    @41
    @0
    @37
    wa
    #
    @1
    @38
    wa
    #
    @2
    @11
    @56
    @41
    @0
    @37
    @0
    @1
    @2
    @39
    @12
    simpll1
    #
    @3
    @37
    @38
    @12
    simplrl
    #
    jca
    @41
    @1
    @38
    @0
    @1
    @2
    @39
    @12
    simpll2
    #
    @3
    @37
    @38
    @12
    simplrr
    #
    jca
    @0
    @1
    @2
    @39
    @12
    simpll3
    #
    @40
    @11
    wps
    simprl
    @57
    @58
    wa
    @2
    @11
    wa
    @56
    cA
    @9
    cB
    @10
    cV
    cD
    cW
    cD
    f1oprg
    imp
    syl22anc
    @4
    @53
    @47
    f1of1
    syl
    @41
    @37
    @38
    @55
    @60
    @62
    @9
    @10
    cD
    prssi
    syl2anc
    @4
    @53
    cD
    @47
    f1ss
    syl2anc
    @41
    @0
    @37
    @2
    @50
    @59
    @60
    @63
    @0
    @37
    @2
    w3a
    @49
    @9
    cA
    cB
    @9
    @10
    cV
    cD
    fvpr1g
    eqcomd
    syl3anc
    @41
    @1
    @38
    @2
    @52
    @61
    @62
    @63
    @1
    @38
    @2
    w3a
    @51
    @10
    cA
    cB
    @9
    @10
    cW
    cD
    fvpr2g
    eqcomd
    syl3anc
    @43
    @48
    @50
    @52
    wa
    #
    wa
    vf
    @47
    @45
    @46
    prex
    @5
    @47
    wceq
    #
    @6
    @48
    @42
    @64
    @4
    cD
    @5
    @47
    f1eq1
    @65
    @35
    @50
    @36
    @52
    @65
    @15
    @49
    @9
    cA
    @5
    @47
    fveq1
    eqeq2d
    @65
    @17
    @51
    @10
    cB
    @5
    @47
    fveq1
    eqeq2d
    anbi12d
    anbi12d
    spcev
    syl12anc
    @41
    @43
    @7
    vf
    @41
    @43
    @7
    @41
    @43
    wa
    #
    @6
    wph
    @41
    @6
    @42
    simprl
    @66
    wch
    wph
    @66
    wps
    wch
    @40
    @11
    wps
    @43
    simplrr
    @66
    @35
    wps
    wch
    wb
    @41
    @6
    @35
    @36
    simprrl
    f1prex.1
    syl
    mpbid
    @66
    @36
    wch
    wph
    wb
    @41
    @6
    @35
    @36
    simprrr
    f1prex.2
    syl
    mpbid
    jca
    ex
    eximdv
    mpd
    ex
    rexlimdvva
    imp
    impbida
end
