include "cword.mm"
include "wcel.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cn0.mm"
include "lencl.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "eqeq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "c0.mm"
include "hasheq0.mm"
include "mpbiri.mm"
include "syl6bi.mm"
include "rgen.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "wa.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "wsbc.mm"
include "swrdcl.mm"
include "ad2antrl.mm"
include "simplr.mm"
include "cfz.mm"
include "simprl.mm"
include "cfzo.mm"
include "fzossfz.mm"
include "cn.mm"
include "simprr.mm"
include "nn0p1nn.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "fzo0end.mm"
include "syl.mm"
include "sseldi.mm"
include "swrd0len.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "vex.mm"
include "sbcie.mm"
include "dfsbcq.mm"
include "syl5bbr.mm"
include "rspcv.mm"
include "syl3c.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "nnge1d.mm"
include "wb.mm"
include "wrdlenge1n0.mm"
include "mpbird.mm"
include "lswcl.mm"
include "oveq1.mm"
include "sbceq1d.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "imbi2d.mm"
include "ovex.mm"
include "3imtr4g.mm"
include "vtocl2ga.mm"
include "mpd.mm"
include "cfn.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "mpbid.mm"
include "swrdccatwrd.mm"
include "eqcomd.mm"
include "sbceq1a.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ex.mm"
include "syl5bi.mm"
include "nn0ind.mm"
include "eqidd.mm"
include "mp2d.mm"

theorem wrdind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vm: setvar m
  assume wrdind.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume wrdind.2: |- ( x = y -> ( ph <-> ch ) )
  assume wrdind.3: |- ( x = ( y ++ <" z "> ) -> ( ph <-> th ) )
  assume wrdind.4: |- ( x = A -> ( ph <-> ta ) )
  assume wrdind.5: |- ps
  assume wrdind.6: |- ( ( y e. Word B /\ z e. B ) -> ( ch -> th ) )

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ch x
  disjoint ph y
  disjoint ph z
  disjoint ta x
  disjoint th x
  disjoint n x
  disjoint A n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint m ph
  disjoint n ph
  assert |- ( A e. Word B -> ta )

  proof
    cA
    cB
    cword
    #
    wcel
    #
    vx
    cv
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    wceq
    #
    wph
    wi
    #
    vx
    @0
    wral
    #
    @4
    @4
    wceq
    #
    wta
    @1
    @4
    cn0
    wcel
    @7
    cB
    cA
    lencl
    @3
    vn
    cv
    #
    wceq
    #
    wph
    wi
    #
    vx
    @0
    wral
    @3
    cc0
    wceq
    #
    wph
    wi
    #
    vx
    @0
    wral
    @3
    vm
    cv
    #
    wceq
    #
    wph
    wi
    #
    vx
    @0
    wral
    #
    @3
    @14
    c1
    caddc
    co
    #
    wceq
    #
    wph
    wi
    #
    vx
    @0
    wral
    #
    @7
    vn
    vm
    @4
    @9
    cc0
    wceq
    #
    @11
    @13
    vx
    @0
    @22
    @10
    @12
    wph
    @9
    cc0
    @3
    eqeq2
    imbi1d
    ralbidv
    @9
    @14
    wceq
    #
    @11
    @16
    vx
    @0
    @23
    @10
    @15
    wph
    @9
    @14
    @3
    eqeq2
    imbi1d
    ralbidv
    @9
    @18
    wceq
    #
    @11
    @20
    vx
    @0
    @24
    @10
    @19
    wph
    @9
    @18
    @3
    eqeq2
    imbi1d
    ralbidv
    @9
    @4
    wceq
    #
    @11
    @6
    vx
    @0
    @25
    @10
    @5
    wph
    @9
    @4
    @3
    eqeq2
    imbi1d
    ralbidv
    @13
    vx
    @0
    @2
    @0
    wcel
    #
    @12
    @2
    c0
    wceq
    #
    wph
    @2
    @0
    hasheq0
    @27
    wph
    wps
    wrdind.5
    wrdind.1
    mpbiri
    syl6bi
    rgen
    @17
    vy
    cv
    #
    chash
    cfv
    #
    @14
    wceq
    #
    wch
    wi
    #
    vy
    @0
    wral
    #
    @14
    cn0
    wcel
    #
    @21
    @16
    @31
    vx
    vy
    @0
    @2
    @28
    wceq
    #
    @15
    @30
    wph
    wch
    @34
    @3
    @29
    @14
    @2
    @28
    chash
    fveq2
    eqeq1d
    wrdind.2
    imbi12d
    cbvralv
    @33
    @32
    @21
    @33
    @32
    wa
    #
    @20
    vx
    @0
    @35
    @26
    @19
    wph
    @35
    @26
    @19
    wa
    #
    wa
    #
    wph
    wph
    vx
    @2
    cc0
    @3
    c1
    cmin
    co
    #
    cop
    csubstr
    co
    #
    @2
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    wsbc
    #
    @37
    wph
    vx
    @39
    wsbc
    #
    @43
    @37
    @39
    @0
    wcel
    #
    @32
    @39
    chash
    cfv
    #
    @14
    wceq
    #
    @44
    @26
    @45
    @35
    @19
    cB
    @2
    cc0
    @38
    swrdcl
    ad2antrl
    #
    @33
    @32
    @36
    simplr
    @37
    @46
    @38
    @18
    c1
    cmin
    co
    #
    @14
    @37
    @26
    @38
    cc0
    @3
    cfz
    co
    #
    wcel
    @46
    @38
    wceq
    @35
    @26
    @19
    simprl
    #
    @37
    cc0
    @3
    cfzo
    co
    #
    @50
    @38
    cc0
    @3
    fzossfz
    @37
    @3
    cn
    wcel
    #
    @38
    @52
    wcel
    @37
    @3
    @18
    cn
    @35
    @26
    @19
    simprr
    #
    @33
    @18
    cn
    wcel
    @32
    @36
    @14
    nn0p1nn
    ad2antrr
    eqeltrd
    #
    @3
    fzo0end
    syl
    sseldi
    cB
    @2
    @38
    swrd0len
    syl2anc
    @37
    @3
    @18
    c1
    cmin
    @54
    oveq1d
    @37
    @14
    cc
    wcel
    #
    c1
    cc
    wcel
    @49
    @14
    wceq
    @33
    @56
    @32
    @36
    @14
    nn0cn
    ad2antrr
    ax-1cn
    @14
    c1
    pncan
    sylancl
    3eqtrd
    @31
    @47
    @44
    wi
    vy
    @39
    @0
    @28
    @39
    wceq
    #
    @30
    @47
    wch
    @44
    @57
    @29
    @46
    @14
    @28
    @39
    chash
    fveq2
    eqeq1d
    wch
    wph
    vx
    @28
    wsbc
    #
    @57
    @44
    wph
    wch
    vx
    @28
    vy
    vex
    wrdind.2
    sbcie
    #
    wph
    vx
    @28
    @39
    dfsbcq
    #
    syl5bbr
    imbi12d
    rspcv
    syl3c
    @37
    @45
    @40
    cB
    wcel
    #
    @44
    @43
    wi
    #
    @48
    @37
    @26
    @2
    c0
    wne
    #
    @61
    @51
    @37
    @63
    c1
    @3
    cle
    wbr
    #
    @37
    @3
    @55
    nnge1d
    @26
    @63
    @64
    wb
    @35
    @19
    cB
    @2
    wrdlenge1n0
    ad2antrl
    mpbird
    cB
    @2
    lswcl
    syl2anc
    @58
    wph
    vx
    @28
    vz
    cv
    #
    cs1
    #
    cconcat
    co
    #
    wsbc
    #
    wi
    @44
    wph
    vx
    @39
    @66
    cconcat
    co
    #
    wsbc
    #
    wi
    @62
    vy
    vz
    @39
    @40
    @0
    cB
    @57
    @58
    @44
    @68
    @70
    @60
    @57
    wph
    vx
    @67
    @69
    @28
    @39
    @66
    cconcat
    oveq1
    sbceq1d
    imbi12d
    @65
    @40
    wceq
    #
    @70
    @43
    @44
    @71
    wph
    vx
    @69
    @42
    @71
    @66
    @41
    @39
    cconcat
    @65
    @40
    s1eq
    oveq2d
    sbceq1d
    imbi2d
    @28
    @0
    wcel
    @65
    cB
    wcel
    wa
    wch
    wth
    @58
    @68
    wrdind.6
    @59
    wph
    wth
    vx
    @67
    @28
    @66
    cconcat
    ovex
    wrdind.3
    sbcie
    3imtr4g
    vtocl2ga
    syl2anc
    mpd
    @37
    @2
    @42
    wceq
    #
    wph
    @43
    wb
    @37
    @26
    @63
    @72
    @51
    @37
    @53
    @63
    @55
    @37
    @2
    cfn
    wcel
    #
    @53
    @63
    wb
    @26
    @73
    @35
    @19
    cB
    @2
    wrdfin
    ad2antrl
    @2
    hashnncl
    syl
    mpbid
    @26
    @63
    wa
    @42
    @2
    cB
    @2
    swrdccatwrd
    eqcomd
    syl2anc
    wph
    vx
    @42
    sbceq1a
    syl
    mpbird
    expr
    ralrimiva
    ex
    syl5bi
    nn0ind
    syl
    @1
    @4
    eqidd
    @6
    @8
    wta
    wi
    vx
    cA
    @0
    @2
    cA
    wceq
    #
    @5
    @8
    wph
    wta
    @74
    @3
    @4
    @4
    @2
    cA
    chash
    fveq2
    eqeq1d
    wrdind.4
    imbi12d
    rspcv
    mp2d
end
