include "ccnv.mm"
include "wfun.mm"
include "cdm.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simpli.mm"
include "funcnvsn.mm"
include "pm3.2i.mm"
include "cnvcnvss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "cnvcnvsn.mm"
include "eqsstr3i.mm"
include "dmsnopss.mm"
include "sstri.mm"
include "ss2in.mm"
include "mp2an.mm"
include "wcel.mm"
include "wn.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "nn0rei.mm"
include "nnrei.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "elfzle2.mm"
include "mto.mm"
include "simpri.mm"
include "sseli.mm"
include "disjsn.mm"
include "mpbir.mm"
include "sseq0.mm"
include "funun.mm"
include "opeq1i.mm"
include "sneqi.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "cnvun.mm"
include "funeqi.mm"
include "dmeqi.mm"
include "dmun.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "nn0zi.mm"
include "nnzi.mm"
include "ltleii.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "fzss2.mm"
include "cn.mm"
include "elfz1end.mm"
include "snssi.mm"
include "unssi.mm"
include "eqsstri.mm"

theorem strlemor1OLD
  let cA: class A
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cX: class X
  assume strlemor.f: |- ( Fun `' `' F /\ dom F C_ ( 1 ... I ) )
  assume strlemor.i: |- I e. NN0
  assume strlemor.o: |- I < J
  assume strlemor.j: |- J e. NN
  assume strlemor.a: |- A = J
  assume strlemor1.g: |- G = ( F u. { <. A , X >. } )


  assert |- ( Fun `' `' G /\ dom G C_ ( 1 ... J ) )

  proof
    cG
    ccnv
    #
    ccnv
    #
    wfun
    #
    cG
    cdm
    #
    c1
    cJ
    cfz
    co
    #
    wss
    @2
    cF
    ccnv
    #
    ccnv
    #
    cX
    cJ
    cop
    csn
    ccnv
    #
    cun
    #
    wfun
    #
    @6
    wfun
    #
    @7
    wfun
    #
    wa
    @6
    cdm
    #
    @7
    cdm
    #
    cin
    #
    c0
    wceq
    #
    @9
    @10
    @11
    @10
    cF
    cdm
    #
    c1
    cI
    cfz
    co
    #
    wss
    #
    strlemor.f
    simpli
    cX
    cJ
    funcnvsn
    pm3.2i
    @14
    @16
    cJ
    csn
    #
    cin
    #
    wss
    #
    @20
    c0
    wceq
    #
    @15
    @12
    @16
    wss
    #
    @13
    @19
    wss
    @21
    @6
    cF
    wss
    @23
    cF
    cnvcnvss
    @6
    cF
    dmss
    ax-mp
    @13
    cJ
    cX
    cop
    #
    csn
    #
    cdm
    #
    @19
    @7
    @25
    wss
    @13
    @26
    wss
    @7
    @25
    ccnv
    #
    ccnv
    #
    @25
    cJ
    cX
    cnvcnvsn
    #
    @25
    cnvcnvss
    eqsstr3i
    @7
    @25
    dmss
    ax-mp
    cJ
    cX
    dmsnopss
    #
    sstri
    @12
    @16
    @13
    @19
    ss2in
    mp2an
    @22
    cJ
    @16
    wcel
    #
    wn
    @31
    cJ
    @17
    wcel
    #
    @32
    cJ
    cI
    cle
    wbr
    #
    cI
    cJ
    clt
    wbr
    @33
    wn
    strlemor.o
    cI
    cJ
    cI
    strlemor.i
    nn0rei
    #
    cJ
    strlemor.j
    nnrei
    #
    ltnlei
    mpbi
    cJ
    c1
    cI
    elfzle2
    mto
    @16
    @17
    cJ
    @10
    @18
    strlemor.f
    simpri
    #
    sseli
    mto
    @16
    cJ
    disjsn
    mpbir
    @14
    @20
    sseq0
    mp2an
    @6
    @7
    funun
    mp2an
    @1
    @8
    @1
    @5
    @27
    cun
    #
    ccnv
    #
    @8
    @0
    @37
    @0
    cF
    @25
    cun
    #
    ccnv
    @37
    cG
    @39
    cG
    cF
    cA
    cX
    cop
    #
    csn
    #
    cun
    @39
    strlemor1.g
    @41
    @25
    cF
    @40
    @24
    cA
    cJ
    cX
    strlemor.a
    opeq1i
    sneqi
    uneq2i
    eqtri
    #
    cnveqi
    cF
    @25
    cnvun
    eqtri
    cnveqi
    @38
    @6
    @28
    cun
    @8
    @5
    @27
    cnvun
    @28
    @7
    @6
    @29
    uneq2i
    eqtri
    eqtri
    funeqi
    mpbir
    @3
    @16
    @26
    cun
    #
    @4
    @3
    @39
    cdm
    @43
    cG
    @39
    @42
    dmeqi
    cF
    @25
    dmun
    eqtri
    @16
    @26
    @4
    @16
    @17
    @4
    @36
    cJ
    cI
    cuz
    cfv
    wcel
    #
    @17
    @4
    wss
    @44
    cI
    cz
    wcel
    cJ
    cz
    wcel
    cI
    cJ
    cle
    wbr
    cI
    strlemor.i
    nn0zi
    cJ
    strlemor.j
    nnzi
    cI
    cJ
    @34
    @35
    strlemor.o
    ltleii
    cI
    cJ
    eluz2
    mpbir3an
    cI
    c1
    cJ
    fzss2
    ax-mp
    sstri
    @26
    @19
    @4
    @30
    cJ
    @4
    wcel
    #
    @19
    @4
    wss
    cJ
    cn
    wcel
    @45
    strlemor.j
    cJ
    elfz1end
    mpbi
    cJ
    @4
    snssi
    ax-mp
    sstri
    unssi
    eqsstri
    pm3.2i
end
