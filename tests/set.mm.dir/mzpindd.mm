include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cvv.mm"
include "elfvex.mm"
include "adantl.mm"
include "cmzpcl.mm"
include "cint.mm"
include "wceq.mm"
include "mzpval.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "cmpt.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "ssrab2.mm"
include "a1i.mm"
include "ovex.mm"
include "zex.mm"
include "constmap.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "wf.mm"
include "simpllr.mm"
include "simpr.mm"
include "elmapg.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "elmap.mm"
include "sylibr.mm"
include "adantlr.mm"
include "jca.mm"
include "zaddcl.mm"
include "simpl.mm"
include "inidm.mm"
include "off.mm"
include "ad2ant2r.mm"
include "3expb.mm"
include "zmulcl.mm"
include "jca32.mm"
include "ex.mm"
include "anbi1i.mm"
include "anbi12i.mm"
include "3imtr4g.mm"
include "ralrimivv.mm"
include "wb.mm"
include "elmzpcl.mm"
include "mpbird.mm"
include "intss1.mm"
include "syl.mm"
include "eqsstrd.mm"
include "sselda.mm"
include "an32s.mm"
include "mpdan.mm"
include "simprbi.mm"

theorem mzpindd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume mzpindd.co: |- ( ( ph /\ f e. ZZ ) -> ch )
  assume mzpindd.pr: |- ( ( ph /\ f e. V ) -> th )
  assume mzpindd.ad: |- ( ( ph /\ ( f : ( ZZ ^m V ) --> ZZ /\ ta ) /\ ( g : ( ZZ ^m V ) --> ZZ /\ et ) ) -> ze )
  assume mzpindd.mu: |- ( ( ph /\ ( f : ( ZZ ^m V ) --> ZZ /\ ta ) /\ ( g : ( ZZ ^m V ) --> ZZ /\ et ) ) -> si )
  assume mzpindd.1: |- ( x = ( ( ZZ ^m V ) X. { f } ) -> ( ps <-> ch ) )
  assume mzpindd.2: |- ( x = ( g e. ( ZZ ^m V ) |-> ( g ` f ) ) -> ( ps <-> th ) )
  assume mzpindd.3: |- ( x = f -> ( ps <-> ta ) )
  assume mzpindd.4: |- ( x = g -> ( ps <-> et ) )
  assume mzpindd.5: |- ( x = ( f oF + g ) -> ( ps <-> ze ) )
  assume mzpindd.6: |- ( x = ( f oF x. g ) -> ( ps <-> si ) )
  assume mzpindd.7: |- ( x = A -> ( ps <-> rh ) )

  disjoint ph x
  disjoint f ph
  disjoint g ph
  disjoint f x
  disjoint g x
  disjoint f g
  disjoint f ps
  disjoint g ps
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint et x
  disjoint x ze
  disjoint si x
  disjoint rh x
  disjoint V x
  disjoint V f
  disjoint V g
  disjoint A x
  disjoint V a
  disjoint V b
  disjoint a x
  disjoint b x
  disjoint a f
  disjoint b f
  disjoint a g
  disjoint b g
  disjoint a b
  assert |- ( ( ph /\ A e. ( mzPoly ` V ) ) -> rh )

  proof
    wph
    cA
    cV
    cmzp
    cfv
    #
    wcel
    #
    wa
    #
    cA
    wps
    vx
    cz
    cz
    cV
    cmap
    co
    #
    cmap
    co
    #
    crab
    #
    wcel
    #
    wrh
    @2
    cV
    cvv
    wcel
    #
    @6
    @1
    @7
    wph
    cA
    cV
    cmzp
    elfvex
    adantl
    wph
    @7
    @1
    @6
    wph
    @7
    wa
    #
    @0
    @5
    cA
    @8
    @0
    cV
    cmzpcl
    cfv
    #
    cint
    #
    @5
    @7
    @0
    @10
    wceq
    wph
    cV
    mzpval
    adantl
    @8
    @5
    @9
    wcel
    #
    @10
    @5
    wss
    @8
    @11
    @5
    @4
    wss
    #
    @3
    vf
    cv
    #
    csn
    cxp
    #
    @5
    wcel
    #
    vf
    cz
    wral
    #
    vg
    @3
    @13
    vg
    cv
    #
    cfv
    #
    cmpt
    #
    @5
    wcel
    #
    vf
    cV
    wral
    #
    wa
    #
    @13
    @17
    caddc
    cof
    co
    #
    @5
    wcel
    #
    @13
    @17
    cmul
    cof
    co
    #
    @5
    wcel
    #
    wa
    #
    vg
    @5
    wral
    vf
    @5
    wral
    #
    wa
    wa
    #
    @8
    @12
    @22
    @28
    @12
    @8
    wps
    vx
    @4
    ssrab2
    a1i
    @8
    @16
    @21
    wph
    @16
    @7
    wph
    @15
    vf
    cz
    wph
    @13
    cz
    wcel
    #
    wa
    @14
    @4
    wcel
    #
    wch
    @15
    @30
    @31
    wph
    @3
    @13
    cz
    cz
    cV
    cmap
    ovex
    #
    zex
    constmap
    adantl
    mzpindd.co
    wps
    wch
    vx
    @14
    @4
    mzpindd.1
    elrab
    sylanbrc
    ralrimiva
    adantr
    @8
    @20
    vf
    cV
    @8
    @13
    cV
    wcel
    #
    wa
    #
    @19
    @4
    wcel
    #
    wth
    @20
    @34
    @3
    cz
    @19
    wf
    @35
    @34
    vg
    @3
    @18
    cz
    @19
    @34
    @17
    @3
    wcel
    #
    wa
    #
    cV
    cz
    @13
    @17
    @37
    cz
    cvv
    wcel
    #
    @7
    @36
    cV
    cz
    @17
    wf
    #
    @38
    @37
    zex
    a1i
    wph
    @7
    @33
    @36
    simpllr
    @34
    @36
    simpr
    @38
    @7
    wa
    @36
    @39
    cz
    cV
    @17
    cvv
    cvv
    elmapg
    biimpa
    syl21anc
    @8
    @33
    @36
    simplr
    ffvelrnd
    @19
    eqid
    fmptd
    cz
    @3
    @19
    zex
    @32
    elmap
    sylibr
    wph
    @33
    wth
    @7
    mzpindd.pr
    adantlr
    wps
    wth
    vx
    @19
    @4
    mzpindd.2
    elrab
    sylanbrc
    ralrimiva
    jca
    wph
    @28
    @7
    wph
    @27
    vf
    vg
    @5
    @5
    wph
    @13
    @4
    wcel
    #
    wta
    wa
    #
    @17
    @4
    wcel
    #
    wet
    wa
    #
    wa
    #
    @23
    @4
    wcel
    #
    wze
    wa
    #
    @25
    @4
    wcel
    #
    wsi
    wa
    #
    wa
    #
    @13
    @5
    wcel
    #
    @17
    @5
    wcel
    #
    wa
    @27
    wph
    @3
    cz
    @13
    wf
    #
    wta
    wa
    #
    @3
    cz
    @17
    wf
    #
    wet
    wa
    #
    wa
    #
    @3
    cz
    @23
    wf
    #
    wze
    wa
    #
    @3
    cz
    @25
    wf
    #
    wsi
    wa
    #
    wa
    #
    @44
    @49
    wph
    @56
    @61
    wph
    @56
    wa
    #
    @58
    @59
    wsi
    @62
    @57
    wze
    @56
    @57
    wph
    @52
    @54
    @57
    wta
    wet
    @52
    @54
    wa
    #
    va
    vb
    @3
    @3
    @3
    caddc
    cz
    cz
    cz
    @13
    @17
    cvv
    cvv
    va
    cv
    #
    cz
    wcel
    vb
    cv
    #
    cz
    wcel
    wa
    #
    @64
    @65
    caddc
    co
    cz
    wcel
    @63
    @64
    @65
    zaddcl
    adantl
    @52
    @54
    simpl
    #
    @52
    @54
    simpr
    #
    @3
    cvv
    wcel
    @63
    @32
    a1i
    #
    @69
    @3
    inidm
    #
    off
    ad2ant2r
    adantl
    wph
    @53
    @55
    wze
    mzpindd.ad
    3expb
    jca
    @56
    @59
    wph
    @52
    @54
    @59
    wta
    wet
    @63
    va
    vb
    @3
    @3
    @3
    cmul
    cz
    cz
    cz
    @13
    @17
    cvv
    cvv
    @66
    @64
    @65
    cmul
    co
    cz
    wcel
    @63
    @64
    @65
    zmulcl
    adantl
    @67
    @68
    @69
    @69
    @70
    off
    ad2ant2r
    adantl
    wph
    @53
    @55
    wsi
    mzpindd.mu
    3expb
    jca32
    ex
    @41
    @53
    @43
    @55
    @40
    @52
    wta
    cz
    @3
    @13
    zex
    @32
    elmap
    anbi1i
    @42
    @54
    wet
    cz
    @3
    @17
    zex
    @32
    elmap
    anbi1i
    anbi12i
    @46
    @58
    @48
    @60
    @45
    @57
    wze
    cz
    @3
    @23
    zex
    @32
    elmap
    anbi1i
    @47
    @59
    wsi
    cz
    @3
    @25
    zex
    @32
    elmap
    anbi1i
    anbi12i
    3imtr4g
    @50
    @41
    @51
    @43
    wps
    wta
    vx
    @13
    @4
    mzpindd.3
    elrab
    wps
    wet
    vx
    @17
    @4
    mzpindd.4
    elrab
    anbi12i
    @24
    @46
    @26
    @48
    wps
    wze
    vx
    @23
    @4
    mzpindd.5
    elrab
    wps
    wsi
    vx
    @25
    @4
    mzpindd.6
    elrab
    anbi12i
    3imtr4g
    ralrimivv
    adantr
    jca32
    @7
    @11
    @29
    wb
    wph
    vg
    @5
    vf
    vg
    vf
    vf
    cV
    elmzpcl
    adantl
    mpbird
    @5
    @9
    intss1
    syl
    eqsstrd
    sselda
    an32s
    mpdan
    @6
    cA
    @4
    wcel
    wrh
    wps
    wrh
    vx
    cA
    @4
    mzpindd.7
    elrab
    simprbi
    syl
end
