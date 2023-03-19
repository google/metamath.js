include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cmin.mm"
include "cphi.mm"
include "cle.mm"
include "cdom.mm"
include "wbr.mm"
include "cfn.mm"
include "wss.mm"
include "fzfi.mm"
include "phibndlem.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "wb.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashdom.mm"
include "sylibr.mm"
include "cn.mm"
include "eluz2nn.mm"
include "phival.mm"
include "syl.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "hashfz1.mm"
include "3syl.mm"
include "eqcomd.mm"
include "3brtr4d.mm"

theorem phibnd
  let cN: class N
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` 2 ) -> ( phi ` N ) <_ ( N - 1 ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    vx
    cv
    cN
    cgcd
    co
    c1
    wceq
    #
    vx
    c1
    cN
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    chash
    cfv
    #
    cN
    cphi
    cfv
    #
    @5
    cle
    @0
    @3
    @6
    cdom
    wbr
    #
    @4
    @7
    cle
    wbr
    #
    @6
    cfn
    wcel
    #
    @0
    @3
    @6
    wss
    @9
    c1
    @5
    fzfi
    #
    vx
    cN
    phibndlem
    @3
    @6
    cfn
    ssdomg
    mpsyl
    @3
    cfn
    wcel
    #
    @11
    @10
    @9
    wb
    @2
    cfn
    wcel
    @3
    @2
    wss
    @13
    c1
    cN
    fzfi
    @1
    vx
    @2
    ssrab2
    @2
    @3
    ssfi
    mp2an
    @12
    @3
    @6
    cfn
    hashdom
    mp2an
    sylibr
    @0
    cN
    cn
    wcel
    #
    @8
    @4
    wceq
    cN
    eluz2nn
    #
    vx
    cN
    phival
    syl
    @0
    @7
    @5
    @0
    @14
    @5
    cn0
    wcel
    @7
    @5
    wceq
    @15
    cN
    nnm1nn0
    @5
    hashfz1
    3syl
    eqcomd
    3brtr4d
end
