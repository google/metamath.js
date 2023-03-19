include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cfa.mm"
include "cfv.mm"
include "cle.mm"
include "cmul.mm"
include "c4.mm"
include "sq2.mm"
include "2t2e4.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "cc.mm"
include "wceq.mm"
include "2cn.mm"
include "expp1.mm"
include "mpan.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "expcl.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "2cnne0.mm"
include "divmuldiv.mm"
include "mpanr12.mm"
include "sylancl.mm"
include "2div2e1.mm"
include "halfcld.mm"
include "mulid1d.mm"
include "3eqtr2rd.mm"
include "wbr.mm"
include "2nn0.mm"
include "faclbnd.mm"
include "cr.mm"
include "wb.mm"
include "2re.mm"
include "peano2nn0.mm"
include "reexpcl.mm"
include "sylancr.mm"
include "faccl.mm"
include "nnred.mm"
include "clt.mm"
include "4re.mm"
include "eqeltri.mm"
include "4pos.mm"
include "breqtrri.mm"
include "pm3.2i.mm"
include "ledivmul.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem faclbnd2
  let cN: class N


  assert |- ( N e. NN0 -> ( ( 2 ^ N ) / 2 ) <_ ( ! ` N ) )

  proof
    cN
    cn0
    wcel
    #
    c2
    cN
    cexp
    co
    #
    c2
    cdiv
    co
    #
    c2
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cN
    cfa
    cfv
    #
    cle
    @0
    @6
    @1
    c2
    cmul
    co
    #
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @2
    c2
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @2
    @0
    @6
    @4
    @9
    cdiv
    co
    @10
    @5
    @9
    @4
    cdiv
    @5
    c4
    @9
    sq2
    2t2e4
    eqtr4i
    oveq2i
    @0
    @4
    @8
    @9
    cdiv
    c2
    cc
    wcel
    #
    @0
    @4
    @8
    wceq
    2cn
    c2
    cN
    expp1
    mpan
    oveq1d
    syl5eq
    @0
    @1
    cc
    wcel
    #
    @13
    @12
    @10
    wceq
    #
    @13
    @0
    @14
    2cn
    c2
    cN
    expcl
    mpan
    #
    2cn
    @14
    @13
    wa
    @13
    c2
    cc0
    wne
    wa
    #
    @17
    @15
    2cnne0
    2cnne0
    @1
    c2
    c2
    c2
    divmuldiv
    mpanr12
    sylancl
    @0
    @12
    @2
    c1
    cmul
    co
    @2
    @11
    c1
    @2
    cmul
    2div2e1
    oveq2i
    @0
    @2
    @0
    @1
    @16
    halfcld
    mulid1d
    syl5eq
    3eqtr2rd
    @0
    @6
    @7
    cle
    wbr
    #
    @4
    @5
    @7
    cmul
    co
    cle
    wbr
    #
    c2
    cn0
    wcel
    @0
    @19
    2nn0
    c2
    cN
    faclbnd
    mpan
    @0
    @4
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @18
    @19
    wb
    #
    @0
    c2
    cr
    wcel
    @3
    cn0
    wcel
    @20
    2re
    cN
    peano2nn0
    c2
    @3
    reexpcl
    sylancr
    @0
    @7
    cN
    faccl
    nnred
    @20
    @21
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    wa
    @22
    @23
    @24
    @5
    c4
    cr
    sq2
    4re
    eqeltri
    cc0
    c4
    @5
    clt
    4pos
    sq2
    breqtrri
    pm3.2i
    @4
    @7
    @5
    ledivmul
    mp3an3
    syl2anc
    mpbird
    eqbrtrd
end
