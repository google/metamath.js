include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "citg2.mm"
include "cfv.mm"
include "cli.mm"
include "c1.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cv.mm"
include "citg1.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "ffvelrnda.mm"
include "itg1cl.mm"
include "syl.mm"
include "fmptd.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wf.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "wral.mm"
include "c0p.mm"
include "simpr.mm"
include "ralimi.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "itg1le.mm"
include "syl3anc.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "3brtr4d.mm"
include "wrex.mm"
include "eqbrtrd.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "climsup.mm"
include "cxr.mm"
include "itg2i1fseq.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "frn.mm"
include "dmmptd.mm"
include "1nn.mm"
include "ne0i.mm"
include "mp1i.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "3syl.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "supxrre.mm"
include "eqtrd.mm"
include "breqtrrd.mm"

theorem itg2i1fseq2
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vy: setvar y
  let vz: setvar z
  assume itg2i1fseq.1: |- ( ph -> F e. MblFn )
  assume itg2i1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2i1fseq.3: |- ( ph -> P : NN --> dom S.1 )
  assume itg2i1fseq.4: |- ( ph -> A. n e. NN ( 0p oR <_ ( P ` n ) /\ ( P ` n ) oR <_ ( P ` ( n + 1 ) ) ) )
  assume itg2i1fseq.5: |- ( ph -> A. x e. RR ( n e. NN |-> ( ( P ` n ) ` x ) ) ~~> ( F ` x ) )
  assume itg2i1fseq.6: |- S = ( m e. NN |-> ( S.1 ` ( P ` m ) ) )
  assume itg2i1fseq2.7: |- ( ph -> M e. RR )
  assume itg2i1fseq2.8: |- ( ( ph /\ k e. NN ) -> ( S.1 ` ( P ` k ) ) <_ M )

  disjoint k m
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint M k
  disjoint M n
  disjoint P k
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint k ph
  disjoint m ph
  disjoint S k
  disjoint k y
  disjoint k z
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M y
  disjoint M z
  disjoint P y
  disjoint P z
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  assert |- ( ph -> S ~~> ( S.2 ` F ) )

  proof
    wph
    cS
    cS
    crn
    #
    cr
    clt
    csup
    #
    cF
    citg2
    cfv
    #
    cli
    wph
    vz
    vk
    cS
    c1
    cn
    nnuz
    wph
    1zzd
    wph
    vm
    cn
    vm
    cv
    #
    cP
    cfv
    #
    citg1
    cfv
    #
    cr
    cS
    wph
    @3
    cn
    wcel
    wa
    @4
    citg1
    cdm
    #
    wcel
    @5
    cr
    wcel
    wph
    cn
    @6
    @3
    cP
    itg2i1fseq.3
    ffvelrnda
    @4
    itg1cl
    syl
    #
    itg2i1fseq.6
    fmptd
    #
    wph
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @9
    cP
    cfv
    #
    citg1
    cfv
    #
    @9
    c1
    caddc
    co
    #
    cP
    cfv
    #
    citg1
    cfv
    #
    @9
    cS
    cfv
    #
    @14
    cS
    cfv
    #
    cle
    @11
    @12
    @6
    wcel
    @15
    @6
    wcel
    #
    @12
    @15
    cle
    cofr
    #
    wbr
    #
    @13
    @16
    cle
    wbr
    wph
    cn
    @6
    @9
    cP
    itg2i1fseq.3
    ffvelrnda
    wph
    cn
    @6
    cP
    wf
    @14
    cn
    wcel
    #
    @19
    @10
    itg2i1fseq.3
    @9
    peano2nn
    #
    cn
    @6
    @14
    cP
    ffvelrn
    syl2an
    wph
    vn
    cv
    #
    cP
    cfv
    #
    @24
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @20
    wbr
    #
    vn
    cn
    wral
    #
    @10
    @21
    wph
    c0p
    @25
    @20
    wbr
    #
    @28
    wa
    #
    vn
    cn
    wral
    @29
    itg2i1fseq.4
    @31
    @28
    vn
    cn
    @30
    @28
    simpr
    ralimi
    syl
    @28
    @21
    vn
    @9
    cn
    @24
    @9
    wceq
    #
    @25
    @12
    @27
    @15
    @20
    @24
    @9
    cP
    fveq2
    @32
    @26
    @14
    cP
    @24
    @9
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspccva
    sylan
    @12
    @15
    itg1le
    syl3anc
    @10
    @17
    @13
    wceq
    wph
    vm
    @9
    @5
    @13
    cn
    cS
    @3
    @9
    wceq
    @4
    @12
    citg1
    @3
    @9
    cP
    fveq2
    fveq2d
    itg2i1fseq.6
    @12
    citg1
    fvex
    fvmpt
    adantl
    #
    @10
    @18
    @16
    wceq
    #
    wph
    @10
    @22
    @34
    @23
    vm
    @14
    @5
    @16
    cn
    cS
    @3
    @14
    wceq
    @4
    @15
    citg1
    @3
    @14
    cP
    fveq2
    fveq2d
    itg2i1fseq.6
    @15
    citg1
    fvex
    fvmpt
    syl
    adantl
    3brtr4d
    wph
    cM
    cr
    wcel
    @17
    cM
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @17
    vz
    cv
    #
    cle
    wbr
    #
    vk
    cn
    wral
    #
    vz
    cr
    wrex
    #
    itg2i1fseq2.7
    wph
    @35
    vk
    cn
    @11
    @17
    @13
    cM
    cle
    @33
    itg2i1fseq2.8
    eqbrtrd
    ralrimiva
    @39
    @36
    vz
    cM
    cr
    @37
    cM
    wceq
    @38
    @35
    vk
    cn
    @37
    cM
    @17
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    climsup
    wph
    @2
    @0
    cxr
    clt
    csup
    #
    @1
    wph
    vx
    cP
    cS
    vm
    vn
    cF
    itg2i1fseq.1
    itg2i1fseq.2
    itg2i1fseq.3
    itg2i1fseq.4
    itg2i1fseq.5
    itg2i1fseq.6
    itg2i1fseq
    wph
    @0
    cr
    wss
    #
    @0
    c0
    wne
    #
    vy
    cv
    #
    @37
    cle
    wbr
    #
    vy
    @0
    wral
    #
    vz
    cr
    wrex
    #
    @42
    @1
    wceq
    wph
    cn
    cr
    cS
    wf
    #
    @43
    @8
    cn
    cr
    cS
    frn
    syl
    wph
    cS
    cdm
    #
    c0
    wne
    @44
    wph
    @50
    cn
    c0
    wph
    vm
    cS
    cn
    @5
    cr
    itg2i1fseq.6
    @7
    dmmptd
    c1
    cn
    wcel
    cn
    c0
    wne
    wph
    1nn
    cn
    c1
    ne0i
    mp1i
    eqnetrd
    @50
    c0
    @0
    c0
    cS
    dm0rn0
    necon3bii
    sylib
    wph
    @48
    @40
    @41
    wph
    @47
    @39
    vz
    cr
    wph
    @49
    cS
    cn
    wfn
    @47
    @39
    wb
    @8
    cn
    cr
    cS
    ffn
    @46
    @38
    vy
    vk
    cn
    cS
    @45
    @17
    @37
    cle
    breq1
    ralrn
    3syl
    rexbidv
    mpbird
    vz
    vy
    @0
    supxrre
    syl3anc
    eqtrd
    breqtrrd
end
