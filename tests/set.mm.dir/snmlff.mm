include "cn.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cmo.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cdiv.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "cfn.mm"
include "cn0.mm"
include "wss.mm"
include "fzfid.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "nndivre.mm"
include "mpancom.mm"
include "clt.mm"
include "nn0ge0d.mm"
include "nnre.mm"
include "nngt0.mm"
include "divge0.mm"
include "syl22anc.mm"
include "cdom.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "wb.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "breqtrd.mm"
include "nncn.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "1red.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "fmpti.mm"

theorem snmlff
  let cA: class A
  let cB: class B
  let cR: class R
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cN: class N
  assume snmlff.f: |- F = ( n e. NN |-> ( ( # ` { k e. ( 1 ... n ) | ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = B } ) / n ) )

  disjoint A n
  disjoint B n
  disjoint k n
  disjoint R n
  disjoint N k
  disjoint N n
  assert |- F : NN --> ( 0 [,] 1 )

  proof
    vn
    cn
    cc0
    c1
    cicc
    co
    #
    cA
    cR
    vk
    cv
    cexp
    co
    cmul
    co
    cR
    cmo
    co
    cfl
    cfv
    cB
    wceq
    #
    vk
    c1
    vn
    cv
    #
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    @2
    cdiv
    co
    #
    cF
    snmlff.f
    @2
    cn
    wcel
    #
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    c1
    cle
    wbr
    #
    @6
    @0
    wcel
    @5
    cr
    wcel
    #
    @7
    @8
    @7
    @5
    @7
    @4
    cfn
    wcel
    #
    @5
    cn0
    wcel
    @7
    @3
    cfn
    wcel
    #
    @4
    @3
    wss
    #
    @12
    @7
    c1
    @2
    fzfid
    #
    @1
    vk
    @3
    ssrab2
    #
    @3
    @4
    ssfi
    sylancl
    #
    @4
    hashcl
    syl
    #
    nn0red
    #
    @5
    @2
    nndivre
    mpancom
    @7
    @11
    cc0
    @5
    cle
    wbr
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @9
    @19
    @7
    @5
    @18
    nn0ge0d
    @2
    nnre
    #
    @2
    nngt0
    #
    @5
    @2
    divge0
    syl22anc
    @7
    @10
    @5
    @2
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @7
    @5
    @2
    @24
    cle
    @7
    @5
    @3
    chash
    cfv
    #
    @2
    cle
    @7
    @5
    @26
    cle
    wbr
    #
    @4
    @3
    cdom
    wbr
    #
    @7
    @13
    @14
    @28
    @15
    @16
    @4
    @3
    cfn
    ssdomg
    mpisyl
    @7
    @12
    @13
    @27
    @28
    wb
    @17
    @15
    @4
    @3
    cfn
    hashdom
    syl2anc
    mpbird
    @7
    @2
    cn0
    wcel
    @26
    @2
    wceq
    @2
    nnnn0
    @2
    hashfz1
    syl
    breqtrd
    @7
    @2
    @2
    nncn
    mulid1d
    breqtrrd
    @7
    @11
    c1
    cr
    wcel
    @20
    @21
    @10
    @25
    wb
    @19
    @7
    1red
    @22
    @23
    @5
    c1
    @2
    ledivmul
    syl112anc
    mpbird
    cc0
    c1
    @6
    0re
    1re
    elicc2i
    syl3anbrc
    fmpti
end
