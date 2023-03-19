include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cdvn.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2i.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "reopn.mm"
include "fzfid.mm"
include "w3a.mm"
include "wf.mm"
include "fzelp1.mm"
include "sylan2.mm"
include "3adant3.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "fzp1elp1.mm"
include "wa.mm"
include "wi.mm"
include "ovex.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "feq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "vtocl.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "nfcv.mm"
include "nfov.mm"
include "nffv.mm"
include "dffn5f.mm"
include "sylib.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "wss.mm"
include "cpm.mm"
include "cn0.mm"
include "ax-resscn.mm"
include "cdm.mm"
include "ffdm.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2g.mm"
include "sylancl.mm"
include "mpbird.mm"
include "adantr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "dvnp1.mm"
include "syl3anc.mm"
include "3eqtr2d.mm"
include "dvmptfsum.mm"
include "syl5eq.mm"

theorem etransclem2
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  let vi: setvar i
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  assume etransclem2.xf: |- F/_ x F
  assume etransclem2.f: |- ( ph -> F : RR --> CC )
  assume etransclem2.dvnf: |- ( ( ph /\ i e. ( 0 ... ( R + 1 ) ) ) -> ( ( RR Dn F ) ` i ) : RR --> CC )
  assume etransclem2.g: |- G = ( x e. RR |-> sum_ i e. ( 0 ... R ) ( ( ( RR Dn F ) ` i ) ` x ) )

  disjoint F i
  disjoint R i
  disjoint R x
  disjoint i x
  disjoint i ph
  disjoint ph x
  disjoint F j
  disjoint i j
  disjoint R j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( RR _D G ) = ( x e. RR |-> sum_ i e. ( 0 ... R ) ( ( ( RR Dn F ) ` ( i + 1 ) ) ` x ) ) )

  proof
    wph
    cr
    cG
    cdv
    co
    cr
    vx
    cr
    cc0
    cR
    cfz
    co
    #
    vx
    cv
    #
    vi
    cv
    #
    cr
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    vi
    csu
    cmpt
    #
    cdv
    co
    vx
    cr
    @0
    @1
    @2
    c1
    caddc
    co
    #
    @3
    cfv
    #
    cfv
    #
    vi
    csu
    cmpt
    cG
    @6
    cr
    cdv
    etransclem2.g
    oveq2i
    wph
    vx
    @5
    @9
    cr
    vi
    @0
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    @11
    @11
    eqid
    #
    tgioo2
    @12
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    cr
    @10
    wcel
    wph
    reopn
    a1i
    wph
    cc0
    cR
    fzfid
    wph
    @2
    @0
    wcel
    #
    @1
    cr
    wcel
    #
    w3a
    #
    cr
    cc
    @1
    @4
    wph
    @13
    cr
    cc
    @4
    wf
    #
    @14
    @13
    wph
    @2
    cc0
    cR
    c1
    caddc
    co
    cfz
    co
    #
    wcel
    #
    @16
    @2
    cc0
    cR
    fzelp1
    etransclem2.dvnf
    sylan2
    #
    3adant3
    wph
    @13
    @14
    simp3
    #
    ffvelrnd
    @15
    cr
    cc
    @1
    @8
    wph
    @13
    cr
    cc
    @8
    wf
    #
    @14
    @13
    wph
    @7
    @17
    wcel
    #
    @21
    @2
    cc0
    cR
    fzp1elp1
    wph
    vj
    cv
    #
    @17
    wcel
    #
    wa
    #
    cr
    cc
    @23
    @3
    cfv
    #
    wf
    #
    wi
    #
    wph
    @22
    wa
    #
    @21
    wi
    vj
    @7
    @2
    c1
    caddc
    ovex
    @23
    @7
    wceq
    #
    @25
    @29
    @27
    @21
    @30
    @24
    @22
    wph
    @23
    @7
    @17
    eleq1
    anbi2d
    @30
    cr
    cc
    @26
    @8
    @23
    @7
    @3
    fveq2
    feq1d
    imbi12d
    wph
    @18
    wa
    #
    @16
    wi
    @28
    vi
    vj
    @2
    @23
    wceq
    #
    @31
    @25
    @16
    @27
    @32
    @18
    @24
    wph
    @2
    @23
    @17
    eleq1
    anbi2d
    @32
    cr
    cc
    @4
    @26
    @2
    @23
    @3
    fveq2
    feq1d
    imbi12d
    etransclem2.dvnf
    chvarv
    vtocl
    sylan2
    #
    3adant3
    @20
    ffvelrnd
    wph
    @13
    wa
    #
    cr
    vx
    cr
    @5
    cmpt
    #
    cdv
    co
    cr
    @4
    cdv
    co
    #
    @8
    vx
    cr
    @9
    cmpt
    #
    @34
    @35
    @4
    cr
    cdv
    @34
    @4
    @35
    @34
    @4
    cr
    wfn
    #
    @4
    @35
    wceq
    @34
    @16
    @38
    @19
    cr
    cc
    @4
    ffn
    syl
    vx
    cr
    @4
    vx
    @2
    @3
    vx
    cr
    cF
    cdvn
    vx
    cr
    nfcv
    vx
    cdvn
    nfcv
    etransclem2.xf
    nfov
    #
    vx
    @2
    nfcv
    nffv
    dffn5f
    sylib
    eqcomd
    oveq2d
    @34
    cr
    cc
    wss
    #
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    @2
    cn0
    wcel
    #
    @8
    @36
    wceq
    @40
    @34
    ax-resscn
    a1i
    wph
    @41
    @13
    wph
    @41
    cF
    cdm
    #
    cc
    cF
    wf
    @43
    cr
    wss
    wa
    #
    wph
    cr
    cc
    cF
    wf
    @44
    etransclem2.f
    cr
    cc
    cF
    ffdm
    syl
    wph
    cc
    cvv
    wcel
    #
    cr
    cvv
    wcel
    @41
    @44
    wb
    @45
    wph
    cnex
    a1i
    reex
    cc
    cr
    cF
    cvv
    cvv
    elpm2g
    sylancl
    mpbird
    adantr
    @13
    @42
    wph
    @2
    cR
    elfznn0
    adantl
    cr
    cF
    @2
    dvnp1
    syl3anc
    @34
    @8
    cr
    wfn
    #
    @8
    @37
    wceq
    @34
    @21
    @46
    @33
    cr
    cc
    @8
    ffn
    syl
    vx
    cr
    @8
    vx
    @7
    @3
    @39
    vx
    @7
    nfcv
    nffv
    dffn5f
    sylib
    3eqtr2d
    dvmptfsum
    syl5eq
end
