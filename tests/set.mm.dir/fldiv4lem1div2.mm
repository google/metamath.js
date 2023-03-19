include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "elnn1uz2.mm"
include "cc0.mm"
include "clt.mm"
include "1lt4.mm"
include "cn0.mm"
include "wb.mm"
include "1nn0.mm"
include "4nn.mm"
include "divfl0.mm"
include "mp2an.mm"
include "mpbi.mm"
include "cr.mm"
include "wne.mm"
include "1re.mm"
include "4re.mm"
include "4ne0.mm"
include "w3a.mm"
include "redivcl.mm"
include "flcld.mm"
include "zred.mm"
include "mp3an.mm"
include "eqlei.mm"
include "mp1i.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "cc.mm"
include "wa.mm"
include "2cnne0.mm"
include "div0.mm"
include "ax-mp.mm"
include "3brtr4d.mm"
include "fldiv4lem1div2uz2.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem fldiv4lem1div2
  let cN: class N


  assert |- ( N e. NN -> ( |_ ` ( N / 4 ) ) <_ ( ( N - 1 ) / 2 ) )

  proof
    cN
    cn
    wcel
    cN
    c1
    wceq
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wo
    cN
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    cN
    elnn1uz2
    @0
    @6
    @1
    @0
    c1
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cc0
    @3
    @5
    cle
    @8
    cc0
    wceq
    #
    @8
    cc0
    cle
    wbr
    @0
    c1
    c4
    clt
    wbr
    #
    @9
    1lt4
    c1
    cn0
    wcel
    c4
    cn
    wcel
    @10
    @9
    wb
    1nn0
    4nn
    c1
    c4
    divfl0
    mp2an
    mpbi
    @8
    cc0
    c1
    cr
    wcel
    #
    c4
    cr
    wcel
    #
    c4
    cc0
    wne
    #
    @8
    cr
    wcel
    1re
    4re
    4ne0
    @11
    @12
    @13
    w3a
    #
    @8
    @14
    @7
    c1
    c4
    redivcl
    flcld
    zred
    mp3an
    eqlei
    mp1i
    @0
    @2
    @7
    cfl
    cN
    c1
    c4
    cdiv
    oveq1
    fveq2d
    @0
    @5
    cc0
    c2
    cdiv
    co
    #
    cc0
    @0
    @4
    cc0
    c2
    cdiv
    @0
    @4
    c1
    c1
    cmin
    co
    cc0
    cN
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    oveq1d
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    @15
    cc0
    wceq
    2cnne0
    c2
    div0
    ax-mp
    syl6eq
    3brtr4d
    cN
    fldiv4lem1div2uz2
    jaoi
    sylbi
end
