include "crn.mm"
include "cuni.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "wcel.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cvol.mm"
include "cdm.mm"
include "cn.mm"
include "wf.mm"
include "frn.mm"
include "syl.mm"
include "mblss.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "elpwi.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cun.mm"
include "inundif.mm"
include "fveq2i.mm"
include "inss1.mm"
include "simp2.mm"
include "syl5ss.mm"
include "ovolsscl.mm"
include "mp3an1.mm"
include "3adant1.mm"
include "difss.mm"
include "ovolun.mm"
include "syl22anc.mm"
include "syl5eqbrr.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "rexrd.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wa.mm"
include "fveq2.mm"
include "ineq2d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "ressxr.mm"
include "supxrcl.mm"
include "simp3.mm"
include "resubcld.mm"
include "ciun.mm"
include "iunin2.mm"
include "wfn.mm"
include "ffn.mm"
include "fniunfv.mm"
include "3syl.mm"
include "3ad2ant1.mm"
include "syl5eq.mm"
include "eqid.mm"
include "ovoliun.mm"
include "eqbrtrrd.mm"
include "wdisj.mm"
include "voliunlem1.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "simpl3.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "ralrn.mm"
include "mpbird.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "xrletrd.mm"
include "readdcld.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "3expia.mm"
include "sylan2.mm"
include "ismbl.mm"
include "sylanbrc.mm"

theorem voliunlem2
  let wph: wff ph
  let vx: setvar x
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cH: class H
  let vk: setvar k
  let vz: setvar z
  let cE: class E
  let cG: class G
  let cS: class S
  assume voliunlem.3: |- ( ph -> F : NN --> dom vol )
  assume voliunlem.5: |- ( ph -> Disj_ i e. NN ( F ` i ) )
  assume voliunlem.6: |- H = ( n e. NN |-> ( vol* ` ( x i^i ( F ` n ) ) ) )

  disjoint i n
  disjoint i x
  disjoint F i
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint n ph
  disjoint ph x
  disjoint k n
  disjoint k z
  disjoint E k
  disjoint n z
  disjoint E n
  disjoint E z
  disjoint i k
  disjoint i z
  disjoint k x
  disjoint F k
  disjoint x z
  disjoint F z
  disjoint G k
  disjoint H k
  disjoint H z
  disjoint S k
  disjoint S x
  disjoint S z
  disjoint k ph
  disjoint ph z
  assert |- ( ph -> U. ran F e. dom vol )

  proof
    wph
    cF
    crn
    #
    cuni
    #
    cr
    wss
    #
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @4
    @3
    @1
    cin
    #
    covol
    cfv
    #
    @3
    @1
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vx
    cr
    cpw
    #
    wral
    @1
    cvol
    cdm
    #
    wcel
    wph
    @0
    @13
    wss
    @2
    wph
    @0
    @14
    @13
    wph
    cn
    @14
    cF
    wf
    #
    @0
    @14
    wss
    voliunlem.3
    cn
    @14
    cF
    frn
    syl
    vx
    @14
    @13
    @3
    @14
    wcel
    @3
    cr
    wss
    #
    @3
    @13
    wcel
    #
    @3
    mblss
    vx
    cr
    selpw
    sylibr
    ssriv
    syl6ss
    @0
    cr
    sspwuni
    sylib
    wph
    @12
    vx
    @13
    @17
    wph
    @16
    @12
    @3
    cr
    elpwi
    wph
    @16
    @5
    @11
    wph
    @16
    @5
    w3a
    #
    @11
    @4
    @10
    cle
    wbr
    @10
    @4
    cle
    wbr
    #
    @18
    @4
    @6
    @8
    cun
    #
    covol
    cfv
    #
    @10
    cle
    @20
    @3
    covol
    @3
    @1
    inundif
    fveq2i
    @18
    @6
    cr
    wss
    @7
    cr
    wcel
    #
    @8
    cr
    wss
    @9
    cr
    wcel
    #
    @21
    @10
    cle
    wbr
    @18
    @6
    @3
    cr
    @3
    @1
    inss1
    #
    wph
    @16
    @5
    simp2
    #
    syl5ss
    @16
    @5
    @22
    wph
    @6
    @3
    wss
    @16
    @5
    @22
    @24
    @6
    @3
    ovolsscl
    mp3an1
    3adant1
    #
    @18
    @8
    @3
    cr
    @3
    @1
    difss
    #
    @25
    syl5ss
    @16
    @5
    @23
    wph
    @8
    @3
    wss
    @16
    @5
    @23
    @27
    @8
    @3
    ovolsscl
    mp3an1
    3adant1
    #
    @6
    @8
    ovolun
    syl22anc
    syl5eqbrr
    @18
    @19
    @7
    @4
    @9
    cmin
    co
    #
    cle
    wbr
    #
    @18
    @7
    caddc
    cH
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    @29
    @18
    @7
    @26
    rexrd
    @18
    @32
    cxr
    wss
    #
    @33
    cxr
    wcel
    @18
    @32
    cr
    cxr
    @18
    cn
    cr
    @31
    wf
    #
    @32
    cr
    wss
    @18
    vk
    cH
    c1
    cn
    nnuz
    @18
    1zzd
    @18
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @36
    cH
    cfv
    #
    @3
    @36
    cF
    cfv
    #
    cin
    #
    covol
    cfv
    #
    cr
    @37
    @39
    @42
    wceq
    @18
    vn
    @36
    @3
    vn
    cv
    #
    cF
    cfv
    #
    cin
    #
    covol
    cfv
    #
    @42
    cn
    cH
    @43
    @36
    wceq
    #
    @45
    @41
    covol
    @47
    @44
    @40
    @3
    @43
    @36
    cF
    fveq2
    ineq2d
    fveq2d
    voliunlem.6
    @41
    covol
    fvex
    fvmpt
    adantl
    @18
    @42
    cr
    wcel
    #
    @37
    @16
    @5
    @48
    wph
    @41
    @3
    wss
    @16
    @5
    @48
    @3
    @40
    inss1
    @41
    @3
    ovolsscl
    mp3an1
    3adant1
    adantr
    eqeltrd
    serfre
    #
    cn
    cr
    @31
    frn
    syl
    ressxr
    syl6ss
    #
    @32
    supxrcl
    syl
    @18
    @29
    @18
    @4
    @9
    wph
    @16
    @5
    simp3
    #
    @28
    resubcld
    rexrd
    #
    @18
    vn
    cn
    @45
    ciun
    #
    covol
    cfv
    @7
    @33
    cle
    @18
    @53
    @6
    covol
    @18
    @53
    @3
    vn
    cn
    @44
    ciun
    #
    cin
    @6
    vn
    cn
    @3
    @44
    iunin2
    @18
    @54
    @1
    @3
    wph
    @16
    @54
    @1
    wceq
    #
    @5
    wph
    @15
    cF
    cn
    wfn
    @55
    voliunlem.3
    cn
    @14
    cF
    ffn
    vn
    cn
    cF
    fniunfv
    3syl
    3ad2ant1
    ineq2d
    syl5eq
    fveq2d
    @18
    @45
    @31
    vn
    cH
    @31
    eqid
    voliunlem.6
    @18
    @45
    cr
    wss
    @43
    cn
    wcel
    #
    @18
    @45
    @3
    cr
    @3
    @44
    inss1
    #
    @25
    syl5ss
    adantr
    @18
    @46
    cr
    wcel
    #
    @56
    @16
    @5
    @58
    wph
    @45
    @3
    wss
    @16
    @5
    @58
    @57
    @45
    @3
    ovolsscl
    mp3an1
    3adant1
    adantr
    ovoliun
    eqbrtrrd
    @18
    @33
    @29
    cle
    wbr
    #
    vz
    cv
    #
    @29
    cle
    wbr
    #
    vz
    @32
    wral
    #
    @18
    @62
    @36
    @31
    cfv
    #
    @29
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @18
    @64
    vk
    cn
    @38
    @63
    @9
    caddc
    co
    @4
    cle
    wbr
    #
    @64
    @18
    vi
    vk
    vn
    @3
    cF
    cH
    wph
    @16
    @15
    @5
    voliunlem.3
    3ad2ant1
    wph
    @16
    vi
    cn
    vi
    cv
    cF
    cfv
    wdisj
    @5
    voliunlem.5
    3ad2ant1
    voliunlem.6
    @25
    @51
    voliunlem1
    @38
    @63
    cr
    wcel
    @23
    @5
    @66
    @64
    wb
    @18
    cn
    cr
    @36
    @31
    @49
    ffvelrnda
    @18
    @23
    @37
    @28
    adantr
    wph
    @16
    @5
    @37
    simpl3
    @63
    @9
    @4
    leaddsub
    syl3anc
    mpbid
    ralrimiva
    @18
    @35
    @31
    cn
    wfn
    @62
    @65
    wb
    @49
    cn
    cr
    @31
    ffn
    @61
    @64
    vz
    vk
    cn
    @31
    @60
    @63
    @29
    cle
    breq1
    ralrn
    3syl
    mpbird
    @18
    @34
    @29
    cxr
    wcel
    @59
    @62
    wb
    @50
    @52
    vz
    @32
    @29
    supxrleub
    syl2anc
    mpbird
    xrletrd
    @18
    @22
    @23
    @5
    @19
    @30
    wb
    @26
    @28
    @51
    @7
    @9
    @4
    leaddsub
    syl3anc
    mpbird
    @18
    @4
    @10
    @51
    @18
    @7
    @9
    @26
    @28
    readdcld
    letri3d
    mpbir2and
    3expia
    sylan2
    ralrimiva
    vx
    @1
    ismbl
    sylanbrc
end
