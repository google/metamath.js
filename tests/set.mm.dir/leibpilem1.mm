include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "wo.mm"
include "elnn0.mm"
include "biimpi.mm"
include "ord.mm"
include "con1d.mm"
include "imp.mm"
include "adantrr.mm"
include "cz.mm"
include "cle.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "wb.mm"
include "nn0z.mm"
include "adantr.mm"
include "odd2np1.mm"
include "syl.mm"
include "cc.mm"
include "zcn.mm"
include "2cn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "eqtrd.mm"
include "id.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "syl6bi.mm"
include "impr.mm"
include "cr.mm"
include "clt.mm"
include "nnm1nn0.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "divge0.mm"
include "syl22anc.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "jca.mm"

theorem leibpilem1
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cG: class G


  assert |- ( ( N e. NN0 /\ ( -. N = 0 /\ -. 2 || N ) ) -> ( N e. NN /\ ( ( N - 1 ) / 2 ) e. NN0 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    wceq
    #
    wn
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    wa
    wa
    #
    cN
    cn
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
    cn0
    wcel
    #
    @0
    @2
    @5
    @3
    @0
    @2
    @5
    @0
    @5
    @1
    @0
    @5
    @1
    @0
    @5
    @1
    wo
    cN
    elnn0
    biimpi
    ord
    con1d
    imp
    adantrr
    #
    @4
    @7
    cz
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @8
    @0
    @2
    @3
    @10
    @0
    @2
    wa
    #
    @3
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
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    @10
    @12
    cN
    cz
    wcel
    #
    @3
    @17
    wb
    @0
    @18
    @2
    cN
    nn0z
    adantr
    vn
    cN
    odd2np1
    syl
    @16
    @10
    vn
    cz
    @13
    cz
    wcel
    #
    @15
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
    @16
    @10
    @19
    @21
    @13
    cz
    @19
    @13
    cc
    wcel
    #
    @21
    @13
    wceq
    @13
    zcn
    @22
    @21
    @14
    c2
    cdiv
    co
    #
    @13
    @22
    @20
    @14
    c2
    cdiv
    @22
    @14
    cc
    wcel
    #
    c1
    cc
    wcel
    @20
    @14
    wceq
    c2
    cc
    wcel
    #
    @22
    @24
    2cn
    c2
    @13
    mulcl
    mpan
    ax-1cn
    @14
    c1
    pncan
    sylancl
    oveq1d
    @22
    @25
    c2
    cc0
    wne
    @23
    @13
    wceq
    2cn
    2ne0
    @13
    c2
    divcan3
    mp3an23
    eqtrd
    syl
    @19
    id
    eqeltrd
    @16
    @21
    @7
    cz
    @16
    @20
    @6
    c2
    cdiv
    @15
    cN
    c1
    cmin
    oveq1
    oveq1d
    eleq1d
    syl5ibcom
    rexlimiv
    syl6bi
    impr
    @4
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @11
    @4
    @6
    @4
    @5
    @6
    cn0
    wcel
    @9
    cN
    nnm1nn0
    syl
    #
    nn0red
    @4
    @6
    @28
    nn0ge0d
    @26
    @4
    2re
    a1i
    @27
    @4
    2pos
    a1i
    @6
    c2
    divge0
    syl22anc
    @7
    elnn0z
    sylanbrc
    jca
end
