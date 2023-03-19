include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "cdvds.mm"
include "wn.mm"
include "eldifi.mm"
include "prmz.mm"
include "syl.mm"
include "wceq.mm"
include "eldifsni.mm"
include "necomd.mm"
include "neneqd.mm"
include "cuz.mm"
include "cfv.mm"
include "wb.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "dvdsprm.mm"
include "sylancr.mm"
include "mtbird.mm"
include "wa.mm"
include "1z.mm"
include "n2dvds1.mm"
include "omoe.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "cn0.mm"
include "prmnn.mm"
include "nnm1nn0.mm"
include "3syl.mm"
include "nn0z.mm"
include "wne.mm"
include "2ne0.mm"
include "dvdsval2.mm"
include "mp3an12.mm"
include "mpbid.mm"
include "prmuz2.mm"
include "uz2m1nn.mm"
include "cr.mm"
include "nnre.mm"
include "nngt0.mm"
include "2re.mm"
include "2pos.mm"
include "divgt0.mm"
include "4syl.mm"
include "elnnz.mm"
include "sylanbrc.mm"

theorem oddprm
  let cN: class N


  assert |- ( N e. ( Prime \ { 2 } ) -> ( ( N - 1 ) / 2 ) e. NN )

  proof
    cN
    cprime
    c2
    csn
    #
    cdif
    wcel
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
    cz
    wcel
    #
    cc0
    @3
    clt
    wbr
    #
    @3
    cn
    wcel
    @1
    c2
    @2
    cdvds
    wbr
    #
    @4
    @1
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    wn
    #
    @6
    @1
    cN
    cprime
    wcel
    #
    @7
    cN
    cprime
    @0
    eldifi
    #
    cN
    prmz
    syl
    @1
    @8
    c2
    cN
    wceq
    #
    @1
    c2
    cN
    @1
    cN
    c2
    cN
    cprime
    c2
    eldifsni
    necomd
    neneqd
    @1
    c2
    c2
    cuz
    cfv
    #
    wcel
    #
    @10
    @8
    @12
    wb
    c2
    cz
    wcel
    #
    @14
    2z
    c2
    uzid
    ax-mp
    @11
    cN
    c2
    dvdsprm
    sylancr
    mtbird
    @7
    @9
    wa
    c1
    cz
    wcel
    c2
    c1
    cdvds
    wbr
    wn
    @6
    1z
    n2dvds1
    cN
    c1
    omoe
    mpanr12
    syl2anc
    @1
    @2
    cn0
    wcel
    #
    @2
    cz
    wcel
    #
    @6
    @4
    wb
    #
    @1
    @10
    cN
    cn
    wcel
    @16
    @11
    cN
    prmnn
    cN
    nnm1nn0
    3syl
    @2
    nn0z
    @15
    c2
    cc0
    wne
    @17
    @18
    2z
    2ne0
    c2
    @2
    dvdsval2
    mp3an12
    3syl
    mpbid
    @1
    @10
    cN
    @13
    wcel
    @2
    cn
    wcel
    #
    @5
    @11
    cN
    prmuz2
    cN
    uz2m1nn
    @19
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @5
    @2
    nnre
    @2
    nngt0
    @20
    @21
    wa
    c2
    cr
    wcel
    cc0
    c2
    clt
    wbr
    @5
    2re
    2pos
    @2
    c2
    divgt0
    mpanr12
    syl2anc
    4syl
    @3
    elnnz
    sylanbrc
end
