include "cn.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cen.mm"
include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "cres.mm"
include "wf1o.mm"
include "nnex.mm"
include "ssex.mm"
include "wf1.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "1z.mm"
include "om2uzf1oi.mm"
include "wceq.mm"
include "wb.mm"
include "nnuz.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "mp2b.mm"
include "f1ores.mm"
include "mpan.mm"
include "f1oeng.mm"
include "syl2anc.mm"
include "adantr.mm"
include "crn.mm"
include "imassrn.mm"
include "cdm.mm"
include "dfdm4.mm"
include "wf.mm"
include "f1of.mm"
include "fdmi.mm"
include "eqtr3i.mm"
include "sseqtri.mm"
include "wi.mm"
include "om2uzuzi.mm"
include "syl6eleqr.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "wfun.mm"
include "f1ofun.mm"
include "funcnvres2.mm"
include "f1oeq1.mm"
include "sylib.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "eleq2d.mm"
include "wfn.mm"
include "f1ofn.mm"
include "fvelrnb.mm"
include "bitr3d.mm"
include "biimpa.mm"
include "fvres.mm"
include "eqeq1d.mm"
include "adantll.mm"
include "sseli.mm"
include "om2uzlt2i.mm"
include "sylan2.mm"
include "breq2.mm"
include "sylan9bb.mm"
include "syldan.mm"
include "biimparc.mm"
include "exp44.mm"
include "imp31.mm"
include "reximdva.mm"
include "syl5.mm"
include "exp4b.mm"
include "com4l.mm"
include "imp.mm"
include "rexlimdv.mm"
include "syld.mm"
include "ex.mm"
include "com3l.mm"
include "ralrimiv.mm"
include "unbnn3.mm"
include "sylancr.mm"
include "entr.mm"

theorem unbenlem
  let vx: setvar x
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let vy: setvar y
  assume unbenlem.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 1 ) |` _om )

  disjoint m n
  disjoint A m
  disjoint A n
  disjoint G m
  disjoint G n
  disjoint m y
  disjoint n y
  disjoint A y
  disjoint G y
  assert |- ( ( A C_ NN /\ A. m e. NN E. n e. A m < n ) -> A ~~ _om )

  proof
    cA
    cn
    wss
    #
    vm
    cv
    #
    vn
    cv
    #
    clt
    wbr
    #
    vn
    cA
    wrex
    #
    vm
    cn
    wral
    #
    wa
    #
    cA
    cG
    ccnv
    #
    cA
    cima
    #
    cen
    wbr
    #
    @8
    com
    cen
    wbr
    #
    cA
    com
    cen
    wbr
    @0
    @9
    @5
    @0
    cA
    cvv
    wcel
    cA
    @8
    @7
    cA
    cres
    #
    wf1o
    #
    @9
    cA
    cn
    nnex
    ssex
    cn
    com
    @7
    wf1
    #
    @0
    @12
    com
    cn
    cG
    wf1o
    #
    cn
    com
    @7
    wf1o
    @13
    @14
    com
    c1
    cuz
    cfv
    #
    cG
    wf1o
    #
    vx
    c1
    cG
    1z
    unbenlem.1
    om2uzf1oi
    cn
    @15
    wceq
    @14
    @16
    wb
    nnuz
    cn
    @15
    com
    cG
    f1oeq3
    ax-mp
    mpbir
    #
    com
    cn
    cG
    f1ocnv
    cn
    com
    @7
    f1of1
    mp2b
    cn
    com
    cA
    @7
    f1ores
    mpan
    #
    cA
    @8
    cvv
    @11
    f1oeng
    syl2anc
    adantr
    @6
    @8
    com
    wss
    vy
    cv
    #
    @1
    wcel
    #
    vm
    @8
    wrex
    #
    vy
    com
    wral
    @10
    @8
    @7
    crn
    #
    com
    @7
    cA
    imassrn
    cG
    cdm
    @22
    com
    cG
    dfdm4
    com
    cn
    cG
    @14
    com
    cn
    cG
    wf
    @17
    com
    cn
    cG
    f1of
    ax-mp
    fdmi
    eqtr3i
    sseqtri
    #
    @6
    @21
    vy
    com
    @0
    @5
    @19
    com
    wcel
    #
    @21
    wi
    @24
    @0
    @5
    @21
    @24
    @0
    @5
    @21
    wi
    @24
    @0
    wa
    #
    @5
    @19
    cG
    cfv
    #
    @2
    clt
    wbr
    #
    vn
    cA
    wrex
    #
    @21
    @24
    @5
    @28
    wi
    #
    @0
    @24
    @26
    cn
    wcel
    @29
    @24
    @26
    @15
    cn
    vx
    @19
    c1
    cG
    1z
    unbenlem.1
    om2uzuzi
    nnuz
    syl6eleqr
    @4
    @28
    vm
    @26
    cn
    @1
    @26
    wceq
    @3
    @27
    vn
    cA
    @1
    @26
    @2
    clt
    breq1
    rexbidv
    rspcv
    syl
    adantr
    @25
    @27
    @21
    vn
    cA
    @24
    @0
    @2
    cA
    wcel
    #
    @27
    @21
    wi
    wi
    @27
    @24
    @0
    @30
    @21
    @27
    @24
    @0
    @30
    @21
    @0
    @30
    wa
    @1
    cG
    @8
    cres
    #
    cfv
    #
    @2
    wceq
    #
    vm
    @8
    wrex
    #
    @27
    @24
    wa
    #
    @21
    @0
    @30
    @34
    @0
    @8
    cA
    @31
    wf1o
    #
    @30
    @34
    wb
    @0
    @8
    cA
    @11
    ccnv
    #
    wf1o
    #
    @36
    @0
    @12
    @38
    @18
    cA
    @8
    @11
    f1ocnv
    syl
    cG
    wfun
    #
    @37
    @31
    wceq
    @38
    @36
    wb
    @14
    @39
    @17
    com
    cn
    cG
    f1ofun
    ax-mp
    cA
    cG
    funcnvres2
    @8
    cA
    @37
    @31
    f1oeq1
    mp2b
    sylib
    @36
    @2
    @31
    crn
    #
    wcel
    #
    @30
    @34
    @36
    @40
    cA
    @2
    @36
    @8
    cA
    @31
    wfo
    @40
    cA
    wceq
    @8
    cA
    @31
    f1ofo
    @8
    cA
    @31
    forn
    syl
    eleq2d
    @36
    @31
    @8
    wfn
    @41
    @34
    wb
    @8
    cA
    @31
    f1ofn
    vm
    @8
    @2
    @31
    fvelrnb
    syl
    bitr3d
    syl
    biimpa
    @35
    @33
    @20
    vm
    @8
    @27
    @24
    @1
    @8
    wcel
    #
    @33
    @20
    wi
    @27
    @24
    @42
    @33
    @20
    @24
    @42
    wa
    #
    @33
    wa
    @20
    @27
    @43
    @33
    @1
    cG
    cfv
    #
    @2
    wceq
    #
    @20
    @27
    wb
    @42
    @33
    @45
    @24
    @42
    @33
    @45
    @42
    @32
    @44
    @2
    @1
    @8
    cG
    fvres
    eqeq1d
    biimpa
    adantll
    @43
    @20
    @26
    @44
    clt
    wbr
    #
    @45
    @27
    @42
    @24
    @1
    com
    wcel
    @20
    @46
    wb
    @8
    com
    @1
    @23
    sseli
    vx
    @19
    @1
    c1
    cG
    1z
    unbenlem.1
    om2uzlt2i
    sylan2
    @44
    @2
    @26
    clt
    breq2
    sylan9bb
    syldan
    biimparc
    exp44
    imp31
    reximdva
    syl5
    exp4b
    com4l
    imp
    rexlimdv
    syld
    ex
    com3l
    imp
    ralrimiv
    vy
    vm
    @8
    unbnn3
    sylancr
    cA
    @8
    com
    entr
    syl2anc
end
