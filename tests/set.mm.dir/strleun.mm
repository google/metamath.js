include "cun.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "cn.mm"
include "wcel.mm"
include "cle.mm"
include "w3a.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "isstruct.mm"
include "mpbi.mm"
include "simp1i.mm"
include "simp2i.mm"
include "simp3i.mm"
include "nnrei.mm"
include "ltleii.mm"
include "letri.mm"
include "mp2an.mm"
include "3pm3.2i.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "pm3.2i.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "sstri.mm"
include "ss2in.mm"
include "clt.mm"
include "fzdisj.mm"
include "sseq0.mm"
include "funun.mm"
include "difundir.mm"
include "funeqi.mm"
include "mpbir.mm"
include "dmun.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "nnzi.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "fzss2.mm"
include "fzss1.mm"
include "unssi.mm"
include "eqsstri.mm"

theorem strleun
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume strleun.f: |- F Struct <. A , B >.
  assume strleun.g: |- G Struct <. C , D >.
  assume strleun.l: |- B < C


  assert |- ( F u. G ) Struct <. A , D >.

  proof
    cF
    cG
    cun
    #
    cA
    cD
    cop
    cstr
    wbr
    cA
    cn
    wcel
    #
    cD
    cn
    wcel
    #
    cA
    cD
    cle
    wbr
    #
    w3a
    @0
    c0
    csn
    #
    cdif
    #
    wfun
    #
    @0
    cdm
    #
    cA
    cD
    cfz
    co
    #
    wss
    @1
    @2
    @3
    @1
    cB
    cn
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @1
    @9
    @10
    w3a
    #
    cF
    @4
    cdif
    #
    wfun
    #
    cF
    cdm
    #
    cA
    cB
    cfz
    co
    #
    wss
    #
    cF
    cA
    cB
    cop
    cstr
    wbr
    @11
    @13
    @16
    w3a
    strleun.f
    cF
    cA
    cB
    isstruct
    mpbi
    #
    simp1i
    #
    simp1i
    #
    cC
    cn
    wcel
    #
    @2
    cC
    cD
    cle
    wbr
    #
    @20
    @2
    @21
    w3a
    #
    cG
    @4
    cdif
    #
    wfun
    #
    cG
    cdm
    #
    cC
    cD
    cfz
    co
    #
    wss
    #
    cG
    cC
    cD
    cop
    cstr
    wbr
    @22
    @24
    @27
    w3a
    strleun.g
    cG
    cC
    cD
    isstruct
    mpbi
    #
    simp1i
    #
    simp2i
    #
    cA
    cC
    cle
    wbr
    #
    @21
    @3
    @10
    cB
    cC
    cle
    wbr
    #
    @31
    @1
    @9
    @10
    @18
    simp3i
    cB
    cC
    cB
    @1
    @9
    @10
    @18
    simp2i
    #
    nnrei
    #
    cC
    @20
    @2
    @21
    @29
    simp1i
    #
    nnrei
    #
    strleun.l
    ltleii
    #
    cA
    cB
    cC
    cA
    @19
    nnrei
    #
    @34
    @36
    letri
    mp2an
    #
    @20
    @2
    @21
    @29
    simp3i
    #
    cA
    cC
    cD
    @38
    @36
    cD
    @30
    nnrei
    #
    letri
    mp2an
    3pm3.2i
    @6
    @12
    @23
    cun
    #
    wfun
    #
    @13
    @24
    wa
    @12
    cdm
    #
    @23
    cdm
    #
    cin
    #
    c0
    wceq
    #
    @43
    @13
    @24
    @11
    @13
    @16
    @17
    simp2i
    @22
    @24
    @27
    @28
    simp2i
    pm3.2i
    @46
    @15
    @26
    cin
    #
    wss
    #
    @48
    c0
    wceq
    #
    @47
    @44
    @15
    wss
    @45
    @26
    wss
    @49
    @44
    @14
    @15
    @12
    cF
    wss
    @44
    @14
    wss
    cF
    @4
    difss
    @12
    cF
    dmss
    ax-mp
    @11
    @13
    @16
    @17
    simp3i
    #
    sstri
    @45
    @25
    @26
    @23
    cG
    wss
    @45
    @25
    wss
    cG
    @4
    difss
    @23
    cG
    dmss
    ax-mp
    @22
    @24
    @27
    @28
    simp3i
    #
    sstri
    @44
    @15
    @45
    @26
    ss2in
    mp2an
    cB
    cC
    clt
    wbr
    @50
    strleun.l
    cA
    cB
    cC
    cD
    fzdisj
    ax-mp
    @46
    @48
    sseq0
    mp2an
    @12
    @23
    funun
    mp2an
    @5
    @42
    cF
    cG
    @4
    difundir
    funeqi
    mpbir
    @7
    @14
    @25
    cun
    @8
    cF
    cG
    dmun
    @14
    @25
    @8
    @14
    @15
    @8
    @51
    cD
    cB
    cuz
    cfv
    wcel
    #
    @15
    @8
    wss
    @53
    cB
    cz
    wcel
    cD
    cz
    wcel
    cB
    cD
    cle
    wbr
    #
    cB
    @33
    nnzi
    cD
    @30
    nnzi
    @32
    @21
    @54
    @37
    @40
    cB
    cC
    cD
    @34
    @36
    @41
    letri
    mp2an
    cB
    cD
    eluz2
    mpbir3an
    cB
    cA
    cD
    fzss2
    ax-mp
    sstri
    @25
    @26
    @8
    @52
    cC
    cA
    cuz
    cfv
    wcel
    #
    @26
    @8
    wss
    @55
    cA
    cz
    wcel
    cC
    cz
    wcel
    @31
    cA
    @19
    nnzi
    cC
    @35
    nnzi
    @39
    cA
    cC
    eluz2
    mpbir3an
    cC
    cA
    cD
    fzss1
    ax-mp
    sstri
    unssi
    eqsstri
    @0
    cA
    cD
    isstruct
    mpbir3an
end
