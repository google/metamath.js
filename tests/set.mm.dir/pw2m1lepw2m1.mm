include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cdiv.mm"
include "1lt2.mm"
include "nncn.mm"
include "1cnd.mm"
include "nncand.mm"
include "oveq2d.mm"
include "cc.mm"
include "2cn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "cz.mm"
include "nnz.mm"
include "peano2zm.mm"
include "syl.mm"
include "expsubd.mm"
include "wceq.mm"
include "exp1.mm"
include "mp1i.mm"
include "3eqtr3d.mm"
include "syl5breqr.mm"
include "crp.mm"
include "cr.mm"
include "wb.mm"
include "2nn.mm"
include "nnm1nn0.mm"
include "nnexpcld.mm"
include "nnrpd.mm"
include "cn0.mm"
include "2z.mm"
include "nnnn0.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "zred.mm"
include "divgt1b.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "nnzd.mm"
include "zltlem1.mm"
include "mpbid.mm"

theorem pw2m1lepw2m1
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( I e. NN -> ( 2 ^ ( I - 1 ) ) <_ ( ( 2 ^ I ) - 1 ) )

  proof
    cI
    cn
    wcel
    #
    c2
    cI
    c1
    cmin
    co
    #
    cexp
    co
    #
    c2
    cI
    cexp
    co
    #
    clt
    wbr
    #
    @2
    @3
    c1
    cmin
    co
    cle
    wbr
    #
    @0
    @4
    c1
    @3
    @2
    cdiv
    co
    #
    clt
    wbr
    #
    @0
    c1
    c2
    @6
    clt
    1lt2
    @0
    c2
    cI
    @1
    cmin
    co
    #
    cexp
    co
    c2
    c1
    cexp
    co
    #
    @6
    c2
    @0
    @8
    c1
    c2
    cexp
    @0
    cI
    c1
    cI
    nncn
    @0
    1cnd
    nncand
    oveq2d
    @0
    c2
    cI
    @1
    c2
    cc
    wcel
    #
    @0
    2cn
    a1i
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    @0
    cI
    cz
    wcel
    @1
    cz
    wcel
    cI
    nnz
    #
    cI
    peano2zm
    syl
    @11
    expsubd
    @10
    @9
    c2
    wceq
    @0
    2cn
    c2
    exp1
    mp1i
    3eqtr3d
    syl5breqr
    @0
    @2
    crp
    wcel
    @3
    cr
    wcel
    @4
    @7
    wb
    @0
    @2
    @0
    c2
    @1
    c2
    cn
    wcel
    @0
    2nn
    a1i
    cI
    nnm1nn0
    nnexpcld
    #
    nnrpd
    @0
    @3
    @0
    c2
    cz
    wcel
    cI
    cn0
    wcel
    @3
    cz
    wcel
    #
    2z
    cI
    nnnn0
    c2
    cI
    zexpcl
    sylancr
    #
    zred
    @2
    @3
    divgt1b
    syl2anc
    mpbird
    @0
    @2
    cz
    wcel
    @13
    @4
    @5
    wb
    @0
    @2
    @12
    nnzd
    @14
    @2
    @3
    zltlem1
    syl2anc
    mpbid
end
