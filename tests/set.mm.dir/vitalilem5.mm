include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "covol.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "0lt1.mm"
include "cmin.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "0re.mm"
include "1re.mm"
include "0le1.mm"
include "ovolicc.mm"
include "mp3an.mm"
include "1m0e1.mm"
include "eqtri.mm"
include "breqtrri.mm"
include "eqeltri.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "cn.mm"
include "cv.mm"
include "ciun.mm"
include "wss.mm"
include "crn.mm"
include "cneg.mm"
include "c2.mm"
include "vitalilem2.mm"
include "simp2d.mm"
include "cvol.mm"
include "cdm.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "cpw.mm"
include "cdif.mm"
include "wf.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "cqs.mm"
include "wer.mm"
include "vitalilem1.mm"
include "erdm.mm"
include "ax-mp.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elqsn0.mm"
include "sylancr.mm"
include "a1i.mm"
include "qsss.mm"
include "syl5eqss.mm"
include "sselda.mm"
include "elpwid.mm"
include "sseld.mm"
include "embantd.mm"
include "ralimdva.mm"
include "mpd.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "syl.mm"
include "unitssre.mm"
include "syl6ss.mm"
include "reex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "anim1i.mm"
include "eldif.mm"
include "ex.mm"
include "mt3d.mm"
include "adantr.mm"
include "cq.mm"
include "cin.mm"
include "wf1o.mm"
include "f1of.mm"
include "inss1.mm"
include "qssre.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "ffvelrnda.mm"
include "shftmbl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "ralrimiva.mm"
include "iunmbl.mm"
include "mblss.mm"
include "ovolss.mm"
include "csu.mm"
include "caddc.mm"
include "cmpt.mm"
include "cseq.mm"
include "eqid.mm"
include "vitalilem4.mm"
include "syl6eqel.mm"
include "cli.mm"
include "cuz.mm"
include "csn.mm"
include "cxp.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "nnuz.mm"
include "xpeq1i.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "seqeq3d.mm"
include "cz.mm"
include "1z.mm"
include "serclim0.mm"
include "syl6eqbr.mm"
include "seqex.mm"
include "c0ex.mm"
include "breldm.mm"
include "ovoliun2.mm"
include "sumeq2dv.mm"
include "cfn.mm"
include "wo.mm"
include "eqimssi.mm"
include "orci.mm"
include "sumz.mm"
include "breqtrd.mm"
include "ovolge0.mm"
include "cxr.mm"
include "wb.mm"
include "ovolcl.mm"
include "0xr.mm"
include "xrletri3.mm"
include "mpbir2and.mm"
include "mto.mm"

theorem vitalilem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vs: setvar s
  let vm: setvar m
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let vu: setvar u
  assume vitali.1: |- .~ = { <. x , y >. | ( ( x e. ( 0 [,] 1 ) /\ y e. ( 0 [,] 1 ) ) /\ ( x - y ) e. QQ ) }
  assume vitali.2: |- S = ( ( 0 [,] 1 ) /. .~ )
  assume vitali.3: |- ( ph -> F Fn S )
  assume vitali.4: |- ( ph -> A. z e. S ( z =/= (/) -> ( F ` z ) e. z ) )
  assume vitali.5: |- ( ph -> G : NN -1-1-onto-> ( QQ i^i ( -u 1 [,] 1 ) ) )
  assume vitali.6: |- T = ( n e. NN |-> { s e. RR | ( s - ( G ` n ) ) e. ran F } )
  assume vitali.7: |- ( ph -> -. ran F e. ( ~P RR \ dom vol ) )

  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint n ph
  disjoint ph x
  disjoint ph z
  disjoint S z
  disjoint T x
  disjoint F n
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint .~ n
  disjoint .~ s
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint k m
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint k ph
  disjoint m v
  disjoint m w
  disjoint m ph
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w z
  disjoint ph w
  disjoint S w
  disjoint T k
  disjoint T m
  disjoint T v
  disjoint T w
  disjoint k s
  disjoint k y
  disjoint F k
  disjoint F m
  disjoint s v
  disjoint s w
  disjoint v y
  disjoint F v
  disjoint w y
  disjoint F w
  disjoint m u
  disjoint .~ m
  disjoint n u
  disjoint s u
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .~ u
  disjoint .~ v
  disjoint .~ w
  assert |- -. ph

  proof
    wph
    cc0
    c1
    cicc
    co
    #
    covol
    cfv
    #
    cc0
    cle
    wbr
    #
    cc0
    @1
    clt
    wbr
    @2
    wn
    cc0
    c1
    @1
    clt
    0lt1
    @1
    c1
    cc0
    cmin
    co
    #
    c1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @1
    @3
    wceq
    0re
    1re
    0le1
    cc0
    c1
    ovolicc
    mp3an
    1m0e1
    eqtri
    #
    breqtrri
    cc0
    @1
    0re
    @1
    c1
    cr
    @4
    1re
    eqeltri
    ltnlei
    mpbi
    wph
    @1
    vm
    cn
    vm
    cv
    #
    cT
    cfv
    #
    ciun
    #
    covol
    cfv
    #
    cc0
    cle
    wph
    @0
    @7
    wss
    #
    @7
    cr
    wss
    #
    @1
    @8
    cle
    wbr
    wph
    cF
    crn
    #
    @0
    wss
    #
    @9
    @7
    c1
    cneg
    #
    c2
    cicc
    co
    wss
    wph
    vx
    vy
    vz
    c.sm
    cS
    cT
    vm
    vn
    cF
    cG
    vs
    vitali.1
    vitali.2
    vitali.3
    vitali.4
    vitali.5
    vitali.6
    vitali.7
    vitalilem2
    simp2d
    wph
    @7
    cvol
    cdm
    #
    wcel
    #
    @10
    wph
    @6
    @14
    wcel
    #
    vm
    cn
    wral
    @15
    wph
    @16
    vm
    cn
    wph
    cn
    @14
    @5
    cT
    wph
    vn
    cn
    vs
    cv
    vn
    cv
    #
    cG
    cfv
    #
    cmin
    co
    @11
    wcel
    vs
    cr
    crab
    #
    @14
    cT
    wph
    @17
    cn
    wcel
    #
    wa
    @11
    @14
    wcel
    #
    @18
    cr
    wcel
    @19
    @14
    wcel
    wph
    @21
    @20
    wph
    @21
    @11
    cr
    cpw
    #
    @14
    cdif
    wcel
    #
    vitali.7
    wph
    @21
    wn
    #
    @23
    wph
    @24
    wa
    @11
    @22
    wcel
    #
    @24
    wa
    @23
    wph
    @25
    @24
    wph
    @11
    cr
    wss
    @25
    wph
    @11
    @0
    cr
    wph
    cS
    @0
    cF
    wf
    #
    @12
    wph
    cF
    cS
    wfn
    vz
    cv
    #
    cF
    cfv
    #
    @0
    wcel
    #
    vz
    cS
    wral
    #
    @26
    vitali.3
    wph
    @27
    c0
    wne
    #
    @28
    @27
    wcel
    #
    wi
    #
    vz
    cS
    wral
    @30
    vitali.4
    wph
    @33
    @29
    vz
    cS
    wph
    @27
    cS
    wcel
    #
    wa
    #
    @31
    @32
    @29
    @35
    c.sm
    cdm
    @0
    wceq
    #
    @27
    @0
    c.sm
    cqs
    #
    wcel
    @31
    @0
    c.sm
    wer
    #
    @36
    vx
    vy
    c.sm
    vitali.1
    vitalilem1
    #
    @0
    c.sm
    erdm
    ax-mp
    @35
    @27
    cS
    @37
    wph
    @34
    simpr
    vitali.2
    syl6eleq
    @0
    @27
    c.sm
    elqsn0
    sylancr
    @35
    @27
    @0
    @28
    @35
    @27
    @0
    wph
    cS
    @0
    cpw
    #
    @27
    wph
    cS
    @37
    @40
    vitali.2
    wph
    @0
    c.sm
    @38
    wph
    @39
    a1i
    qsss
    syl5eqss
    sselda
    elpwid
    sseld
    embantd
    ralimdva
    mpd
    vz
    cS
    @0
    cF
    ffnfv
    sylanbrc
    cS
    @0
    cF
    frn
    syl
    unitssre
    syl6ss
    @11
    cr
    reex
    elpw2
    sylibr
    anim1i
    @11
    @22
    @14
    eldif
    sylibr
    ex
    mt3d
    adantr
    wph
    cn
    cr
    @17
    cG
    wph
    cn
    cq
    @13
    c1
    cicc
    co
    #
    cin
    #
    cG
    wf
    #
    @42
    cr
    wss
    cn
    cr
    cG
    wf
    wph
    cn
    @42
    cG
    wf1o
    @43
    vitali.5
    cn
    @42
    cG
    f1of
    syl
    @42
    cq
    cr
    cq
    @41
    inss1
    qssre
    sstri
    cn
    @42
    cr
    cG
    fss
    sylancl
    ffvelrnda
    vs
    @11
    @18
    shftmbl
    syl2anc
    vitali.6
    fmptd
    ffvelrnda
    #
    ralrimiva
    @6
    vm
    iunmbl
    syl
    @7
    mblss
    syl
    #
    @0
    @7
    ovolss
    syl2anc
    wph
    @8
    cc0
    wceq
    #
    @8
    cc0
    cle
    wbr
    #
    cc0
    @8
    cle
    wbr
    #
    wph
    @8
    cn
    @6
    covol
    cfv
    #
    vm
    csu
    #
    cc0
    cle
    wph
    @6
    caddc
    vm
    cn
    @49
    cmpt
    #
    c1
    cseq
    #
    vm
    @51
    @52
    eqid
    @51
    eqid
    wph
    @5
    cn
    wcel
    wa
    #
    @16
    @6
    cr
    wss
    @44
    @6
    mblss
    syl
    @53
    @49
    cc0
    cr
    wph
    vx
    vy
    vz
    c.sm
    cS
    cT
    vm
    vn
    cF
    cG
    vs
    vitali.1
    vitali.2
    vitali.3
    vitali.4
    vitali.5
    vitali.6
    vitali.7
    vitalilem4
    #
    0re
    syl6eqel
    wph
    @52
    cc0
    cli
    wbr
    @52
    cli
    cdm
    wcel
    wph
    @52
    caddc
    c1
    cuz
    cfv
    #
    cc0
    csn
    #
    cxp
    #
    c1
    cseq
    #
    cc0
    cli
    wph
    @51
    @57
    caddc
    c1
    wph
    @51
    vm
    cn
    cc0
    cmpt
    #
    @57
    wph
    vm
    cn
    @49
    cc0
    @54
    mpteq2dva
    cn
    @56
    cxp
    @59
    @57
    vm
    cn
    cc0
    fconstmpt
    cn
    @55
    @56
    nnuz
    xpeq1i
    eqtr3i
    syl6eq
    seqeq3d
    c1
    cz
    wcel
    @58
    cc0
    cli
    wbr
    1z
    c1
    serclim0
    ax-mp
    syl6eqbr
    @52
    cc0
    cli
    caddc
    @51
    c1
    seqex
    c0ex
    breldm
    syl
    ovoliun2
    wph
    @50
    cn
    cc0
    vm
    csu
    #
    cc0
    wph
    cn
    @49
    cc0
    vm
    @54
    sumeq2dv
    cn
    @55
    wss
    #
    cn
    cfn
    wcel
    #
    wo
    @60
    cc0
    wceq
    @61
    @62
    cn
    @55
    nnuz
    eqimssi
    orci
    cn
    vm
    c1
    sumz
    ax-mp
    syl6eq
    breqtrd
    wph
    @10
    @48
    @45
    @7
    ovolge0
    syl
    wph
    @8
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    @46
    @47
    @48
    wa
    wb
    wph
    @10
    @63
    @45
    @7
    ovolcl
    syl
    0xr
    @8
    cc0
    xrletri3
    sylancl
    mpbir2and
    breqtrd
    mto
end
