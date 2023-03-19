include "cn.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "ax-1cn.mm"
include "cuz.mm"
include "cfv.mm"
include "eqimss2i.mm"
include "nnex.mm"
include "climconst2.mm"
include "sylancr.mm"
include "ovexd.mm"
include "basellem6.mm"
include "a1i.mm"
include "cv.mm"
include "wf.mm"
include "wss.mm"
include "elexi.mm"
include "fconst.mm"
include "snssd.mm"
include "fss.mm"
include "ffvelrnda.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylan.mm"
include "peano2nnd.mm"
include "nnrecred.mm"
include "recnd.mm"
include "fmptd.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "climmul.mm"
include "mul01i.mm"
include "syl6breq.mm"
include "1ex.mm"
include "mulcl.mm"
include "adantl.mm"
include "off.mm"
include "climadd.mm"
include "trud.mm"
include "1p0e1.mm"
include "breqtri.mm"

theorem basellem7
  let cA: class A
  let vn: setvar n
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let cH: class H
  let vj: setvar j
  let cM: class M
  let cJ: class J
  let cK: class K
  let cN: class N
  assume basel.g: |- G = ( n e. NN |-> ( 1 / ( ( 2 x. n ) + 1 ) ) )
  assume basellem7.2: |- A e. CC


  assert |- ( ( NN X. { 1 } ) oF + ( ( NN X. { A } ) oF x. G ) ) ~~> 1

  proof
    cn
    c1
    csn
    #
    cxp
    #
    cn
    cA
    csn
    #
    cxp
    #
    cG
    cmul
    cof
    #
    co
    #
    caddc
    cof
    #
    co
    #
    c1
    cc0
    caddc
    co
    #
    c1
    cli
    @7
    @8
    cli
    wbr
    wtru
    c1
    cc0
    vk
    @1
    @5
    @7
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    #
    wtru
    c1
    cc
    wcel
    #
    c1
    cz
    wcel
    #
    @1
    c1
    cli
    wbr
    ax-1cn
    @9
    c1
    c1
    cn
    cn
    c1
    cuz
    cfv
    nnuz
    eqimss2i
    #
    nnex
    climconst2
    sylancr
    wtru
    @1
    @5
    @6
    ovexd
    wtru
    @5
    cA
    cc0
    cmul
    co
    cc0
    cli
    wtru
    cA
    cc0
    vk
    @3
    cG
    @5
    c1
    cvv
    cn
    nnuz
    @9
    wtru
    cA
    cc
    wcel
    #
    @11
    @3
    cA
    cli
    wbr
    basellem7.2
    @9
    cA
    c1
    cn
    @12
    nnex
    climconst2
    sylancr
    wtru
    @3
    cG
    @4
    ovexd
    cG
    cc0
    cli
    wbr
    wtru
    vn
    cG
    basel.g
    basellem6
    a1i
    wtru
    cn
    cc
    vk
    cv
    #
    @3
    wtru
    cn
    @2
    @3
    wf
    @2
    cc
    wss
    cn
    cc
    @3
    wf
    #
    cn
    cA
    cA
    cc
    basellem7.2
    elexi
    fconst
    wtru
    cA
    cc
    @13
    wtru
    basellem7.2
    a1i
    snssd
    cn
    @2
    cc
    @3
    fss
    sylancr
    #
    ffvelrnda
    wtru
    cn
    cc
    @14
    cG
    wtru
    vn
    cn
    c1
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cc
    cG
    wtru
    @17
    cn
    wcel
    #
    wa
    #
    @20
    @22
    @19
    @22
    @18
    wtru
    c2
    cn
    wcel
    #
    @21
    @18
    cn
    wcel
    @23
    wtru
    2nn
    a1i
    c2
    @17
    nnmulcl
    sylan
    peano2nnd
    nnrecred
    recnd
    basel.g
    fmptd
    #
    ffvelrnda
    wtru
    cn
    cn
    @14
    @3
    cfv
    #
    @14
    cG
    cfv
    #
    cmul
    cn
    @3
    cG
    cvv
    cvv
    @14
    wtru
    @15
    @3
    cn
    wfn
    @16
    cn
    cc
    @3
    ffn
    syl
    wtru
    cn
    cc
    cG
    wf
    cG
    cn
    wfn
    @24
    cn
    cc
    cG
    ffn
    syl
    cn
    cvv
    wcel
    wtru
    nnex
    a1i
    #
    @27
    cn
    inidm
    #
    wtru
    @14
    cn
    wcel
    wa
    #
    @25
    eqidd
    @29
    @26
    eqidd
    ofval
    climmul
    cA
    basellem7.2
    mul01i
    syl6breq
    wtru
    cn
    cc
    @14
    @1
    wtru
    cn
    @0
    @1
    wf
    #
    @0
    cc
    wss
    cn
    cc
    @1
    wf
    cn
    c1
    1ex
    fconst
    #
    wtru
    c1
    cc
    @10
    wtru
    ax-1cn
    a1i
    snssd
    cn
    @0
    cc
    @1
    fss
    sylancr
    ffvelrnda
    wtru
    cn
    cc
    @14
    @5
    wtru
    vx
    vy
    cn
    cn
    cn
    cmul
    cc
    cc
    cc
    @3
    cG
    cvv
    cvv
    vx
    cv
    #
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    @32
    @33
    cmul
    co
    cc
    wcel
    wtru
    @32
    @33
    mulcl
    adantl
    @16
    @24
    @27
    @27
    @28
    off
    #
    ffvelrnda
    wtru
    cn
    cn
    @14
    @1
    cfv
    #
    @14
    @5
    cfv
    #
    caddc
    cn
    @1
    @5
    cvv
    cvv
    @14
    wtru
    @30
    @1
    cn
    wfn
    @30
    wtru
    @31
    a1i
    cn
    @0
    @1
    ffn
    syl
    wtru
    cn
    cc
    @5
    wf
    @5
    cn
    wfn
    @34
    cn
    cc
    @5
    ffn
    syl
    @27
    @27
    @28
    @29
    @35
    eqidd
    @29
    @36
    eqidd
    ofval
    climadd
    trud
    1p0e1
    breqtri
end
