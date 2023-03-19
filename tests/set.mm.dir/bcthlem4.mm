include "c1st.mm"
include "cv.mm"
include "ccom.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cbl.mm"
include "co.mm"
include "crn.mm"
include "cuni.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "wcel.mm"
include "wex.mm"
include "cms.mm"
include "cca.mm"
include "cme.mm"
include "cxmt.mm"
include "cmetmet.mm"
include "syl.mm"
include "metxmet.mm"
include "bcthlem2.mm"
include "c2nd.mm"
include "clt.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "cr.mm"
include "cc0.mm"
include "elrp.mm"
include "nnrecl.mm"
include "sylbi.mm"
include "adantl.mm"
include "caddc.mm"
include "peano2nn.mm"
include "cxp.mm"
include "ccl.mm"
include "wss.mm"
include "w3a.mm"
include "wral.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "bcthlem1.mm"
include "expr.mm"
include "mpd.mm"
include "mpbid.mm"
include "simp2d.mm"
include "adantlr.mm"
include "wi.mm"
include "simp1d.mm"
include "xp2nd.mm"
include "rpred.mm"
include "nnrecre.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "breq1d.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "ralrimiva.mm"
include "caubl.mm"
include "cmetcau.mm"
include "syl2anc.mm"
include "wfun.mm"
include "cvv.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofun.mm"
include "ax-mp.mm"
include "vex.mm"
include "cofunexg.mm"
include "mp2an.mm"
include "eldm.mm"
include "sylib.mm"
include "1nn.mm"
include "bcthlem3.mm"
include "mp3an3.mm"
include "cop.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "wn.mm"
include "ctop.mm"
include "mopntop.mm"
include "cxr.mm"
include "xp1st.mm"
include "rpxrd.mm"
include "blssm.mm"
include "1st2nd2.mm"
include "syl6reqr.mm"
include "mopnuni.mm"
include "3sstr3d.mm"
include "eqid.mm"
include "sscls.mm"
include "simp3d.mm"
include "sstrd.mm"
include "3adant2.mm"
include "syl3an3.mm"
include "sseldd.mm"
include "eldifbd.mm"
include "3expa.mm"
include "eluni2.mm"
include "wfn.mm"
include "ccld.mm"
include "wf.mm"
include "ffn.mm"
include "eleq2.mm"
include "rexrn.mm"
include "syl5bb.mm"
include "notbid.mm"
include "ralnex.mm"
include "syl6bbr.mm"
include "biimpar.mm"
include "syldan.mm"
include "eldifd.mm"
include "ne0i.mm"
include "exlimddv.mm"

theorem bcthlem4
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cR: class R
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vn: setvar n
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vy: setvar y
  assume bcth.2: |- J = ( MetOpen ` D )
  assume bcthlem.4: |- ( ph -> D e. ( CMet ` X ) )
  assume bcthlem.5: |- F = ( k e. NN , z e. ( X X. RR+ ) |-> { <. x , r >. | ( ( x e. X /\ r e. RR+ ) /\ ( r < ( 1 / k ) /\ ( ( cls ` J ) ` ( x ( ball ` D ) r ) ) C_ ( ( ( ball ` D ) ` z ) \ ( M ` k ) ) ) ) } )
  assume bcthlem.6: |- ( ph -> M : NN --> ( Clsd ` J ) )
  assume bcthlem.7: |- ( ph -> R e. RR+ )
  assume bcthlem.8: |- ( ph -> C e. X )
  assume bcthlem.9: |- ( ph -> g : NN --> ( X X. RR+ ) )
  assume bcthlem.10: |- ( ph -> ( g ` 1 ) = <. C , R >. )
  assume bcthlem.11: |- ( ph -> A. k e. NN ( g ` ( k + 1 ) ) e. ( k F ( g ` k ) ) )

  disjoint k r
  disjoint k x
  disjoint k z
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint C r
  disjoint C x
  disjoint g k
  disjoint g r
  disjoint g x
  disjoint g z
  disjoint D g
  disjoint D k
  disjoint D r
  disjoint D x
  disjoint D z
  disjoint F g
  disjoint F k
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J g
  disjoint J k
  disjoint J r
  disjoint J x
  disjoint J z
  disjoint M g
  disjoint M k
  disjoint M r
  disjoint M x
  disjoint M z
  disjoint k ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint R x
  disjoint X g
  disjoint X k
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint k n
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint A r
  disjoint A x
  disjoint A z
  disjoint B k
  disjoint B r
  disjoint B x
  disjoint B z
  disjoint g m
  disjoint g n
  disjoint g y
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n y
  disjoint D n
  disjoint r y
  disjoint x y
  disjoint y z
  disjoint D y
  disjoint F n
  disjoint J m
  disjoint J n
  disjoint J y
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint m ph
  disjoint n ph
  disjoint X m
  disjoint X n
  disjoint X y
  assert |- ( ph -> ( ( C ( ball ` D ) R ) \ U. ran M ) =/= (/) )

  proof
    wph
    c1st
    vg
    cv
    #
    ccom
    #
    vx
    cv
    #
    cJ
    clm
    cfv
    #
    wbr
    #
    cC
    cR
    cD
    cbl
    cfv
    #
    co
    #
    cM
    crn
    #
    cuni
    #
    cdif
    #
    c0
    wne
    #
    vx
    wph
    @1
    @3
    cdm
    wcel
    #
    @4
    vx
    wex
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    @1
    cD
    cca
    cfv
    wcel
    @11
    bcthlem.4
    wph
    cD
    vn
    @0
    cX
    vr
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    wph
    @12
    @13
    bcthlem.4
    cD
    cX
    cmetmet
    syl
    cD
    cX
    metxmet
    syl
    #
    bcthlem.9
    wph
    vx
    vz
    cC
    cD
    cR
    vg
    vk
    vn
    cF
    cJ
    cM
    cX
    vr
    bcth.2
    bcthlem.4
    bcthlem.5
    bcthlem.6
    bcthlem.7
    bcthlem.8
    bcthlem.9
    bcthlem.10
    bcthlem.11
    bcthlem2
    wph
    vn
    cv
    #
    @0
    cfv
    #
    c2nd
    cfv
    #
    vr
    cv
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    vr
    crp
    wph
    @19
    crp
    wcel
    #
    wa
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    @19
    clt
    wbr
    #
    vm
    cn
    wrex
    #
    @21
    @22
    @27
    wph
    @22
    @19
    cr
    wcel
    #
    cc0
    @19
    clt
    wbr
    wa
    @27
    @19
    elrp
    @19
    vm
    nnrecl
    sylbi
    adantl
    @23
    @26
    @21
    vm
    cn
    @23
    @24
    cn
    wcel
    #
    wa
    #
    @24
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @26
    @31
    @0
    cfv
    #
    c2nd
    cfv
    #
    @19
    clt
    wbr
    #
    @21
    @29
    @32
    @23
    @24
    peano2nn
    #
    adantl
    @30
    @34
    @25
    clt
    wbr
    #
    @26
    @35
    wph
    @29
    @37
    @22
    wph
    @29
    wa
    #
    @33
    cX
    crp
    cxp
    #
    wcel
    #
    @37
    @33
    @5
    cfv
    #
    cJ
    ccl
    cfv
    cfv
    #
    @24
    @0
    cfv
    #
    @5
    cfv
    #
    @24
    cM
    cfv
    #
    cdif
    #
    wss
    #
    @38
    @33
    @24
    @43
    cF
    co
    #
    wcel
    #
    @40
    @37
    @47
    w3a
    #
    wph
    vk
    cv
    #
    c1
    caddc
    co
    #
    @0
    cfv
    #
    @51
    @51
    @0
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    cn
    wral
    @29
    @49
    bcthlem.11
    @56
    @49
    vk
    @24
    cn
    @51
    @24
    wceq
    #
    @53
    @33
    @55
    @48
    @57
    @52
    @31
    @0
    @51
    @24
    c1
    caddc
    oveq1
    fveq2d
    @57
    @51
    @24
    @54
    @43
    cF
    @57
    id
    @51
    @24
    @0
    fveq2
    oveq12d
    eleq12d
    rspccva
    sylan
    @38
    @43
    @39
    wcel
    #
    @49
    @50
    wb
    #
    wph
    cn
    @39
    @24
    @0
    bcthlem.9
    ffvelrnda
    wph
    @29
    @58
    @59
    wph
    vx
    vz
    @24
    @43
    @33
    cD
    vk
    cF
    cJ
    cM
    cX
    vr
    bcth.2
    bcthlem.4
    bcthlem.5
    bcthlem1
    expr
    mpd
    mpbid
    #
    simp2d
    adantlr
    @30
    @34
    cr
    wcel
    #
    @25
    cr
    wcel
    #
    @28
    @37
    @26
    wa
    @35
    wi
    wph
    @29
    @61
    @22
    @38
    @34
    @38
    @40
    @34
    crp
    wcel
    @38
    @40
    @37
    @47
    @60
    simp1d
    #
    @33
    cX
    crp
    xp2nd
    syl
    #
    rpred
    adantlr
    @29
    @62
    @23
    @24
    nnrecre
    adantl
    @22
    @28
    wph
    @29
    @19
    rpre
    ad2antlr
    @34
    @25
    @19
    lttr
    syl3anc
    mpand
    @20
    @35
    vn
    @31
    cn
    @16
    @31
    wceq
    #
    @18
    @34
    @19
    clt
    @65
    @17
    @33
    c2nd
    @16
    @31
    @0
    fveq2
    fveq2d
    breq1d
    rspcev
    syl6an
    rexlimdva
    mpd
    ralrimiva
    caubl
    cD
    @1
    cJ
    cX
    bcth.2
    cmetcau
    syl2anc
    vx
    @1
    @3
    c1st
    wfun
    #
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    cvv
    cvv
    c1st
    wfo
    @66
    fo1st
    cvv
    cvv
    c1st
    fofun
    ax-mp
    vg
    vex
    c1st
    @0
    cvv
    cofunexg
    mp2an
    eldm
    sylib
    wph
    @4
    wa
    #
    @2
    @9
    wcel
    @10
    @67
    @2
    @6
    @8
    @67
    @2
    c1
    @0
    cfv
    #
    @5
    cfv
    #
    @6
    wph
    @4
    c1
    cn
    wcel
    @2
    @69
    wcel
    1nn
    wph
    vx
    vz
    c1
    cC
    cD
    cR
    vg
    vk
    cF
    cJ
    cM
    cX
    vr
    bcth.2
    bcthlem.4
    bcthlem.5
    bcthlem.6
    bcthlem.7
    bcthlem.8
    bcthlem.9
    bcthlem.10
    bcthlem.11
    bcthlem3
    mp3an3
    wph
    @69
    @6
    wceq
    @4
    wph
    @69
    cC
    cR
    cop
    #
    @5
    cfv
    @6
    wph
    @68
    @70
    @5
    bcthlem.10
    fveq2d
    cC
    cR
    @5
    df-ov
    syl6eqr
    adantr
    eleqtrd
    wph
    @4
    @2
    @45
    wcel
    #
    wn
    #
    vm
    cn
    wral
    #
    @2
    @8
    wcel
    #
    wn
    #
    @67
    @72
    vm
    cn
    wph
    @4
    @29
    @72
    wph
    @4
    @29
    w3a
    #
    @2
    @44
    @45
    @76
    @41
    @46
    @2
    wph
    @29
    @41
    @46
    wss
    @4
    @38
    @41
    @42
    @46
    @38
    cJ
    ctop
    wcel
    #
    @41
    cJ
    cuni
    #
    wss
    @41
    @42
    wss
    wph
    @77
    @29
    wph
    @14
    @77
    @15
    cD
    cJ
    cX
    bcth.2
    mopntop
    syl
    adantr
    @38
    @33
    c1st
    cfv
    #
    @34
    @5
    co
    #
    cX
    @41
    @78
    @38
    @14
    @79
    cX
    wcel
    #
    @34
    cxr
    wcel
    @80
    cX
    wss
    wph
    @14
    @29
    @15
    adantr
    @38
    @40
    @81
    @63
    @33
    cX
    crp
    xp1st
    syl
    @38
    @34
    @64
    rpxrd
    cD
    @79
    @34
    cX
    blssm
    syl3anc
    @38
    @41
    @79
    @34
    cop
    #
    @5
    cfv
    @80
    @38
    @33
    @82
    @5
    @38
    @40
    @33
    @82
    wceq
    @63
    @33
    cX
    crp
    1st2nd2
    syl
    fveq2d
    @79
    @34
    @5
    df-ov
    syl6reqr
    wph
    cX
    @78
    wceq
    #
    @29
    wph
    @14
    @83
    @15
    cD
    cJ
    cX
    bcth.2
    mopnuni
    syl
    adantr
    3sstr3d
    @41
    cJ
    @78
    @78
    eqid
    sscls
    syl2anc
    @38
    @40
    @37
    @47
    @60
    simp3d
    sstrd
    3adant2
    @29
    wph
    @4
    @32
    @2
    @41
    wcel
    @36
    wph
    vx
    vz
    @31
    cC
    cD
    cR
    vg
    vk
    cF
    cJ
    cM
    cX
    vr
    bcth.2
    bcthlem.4
    bcthlem.5
    bcthlem.6
    bcthlem.7
    bcthlem.8
    bcthlem.9
    bcthlem.10
    bcthlem.11
    bcthlem3
    syl3an3
    sseldd
    eldifbd
    3expa
    ralrimiva
    wph
    @75
    @73
    wph
    @75
    @71
    vm
    cn
    wrex
    #
    wn
    @73
    wph
    @74
    @84
    @74
    @2
    vy
    cv
    #
    wcel
    #
    vy
    @7
    wrex
    #
    wph
    @84
    vy
    @2
    @7
    eluni2
    wph
    cM
    cn
    wfn
    #
    @87
    @84
    wb
    wph
    cn
    cJ
    ccld
    cfv
    #
    cM
    wf
    @88
    bcthlem.6
    cn
    @89
    cM
    ffn
    syl
    @86
    @71
    vy
    vm
    cn
    cM
    @85
    @45
    @2
    eleq2
    rexrn
    syl
    syl5bb
    notbid
    @71
    vm
    cn
    ralnex
    syl6bbr
    biimpar
    syldan
    eldifd
    @9
    @2
    ne0i
    syl
    exlimddv
end
