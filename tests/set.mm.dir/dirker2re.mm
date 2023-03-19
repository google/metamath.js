include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "csin.mm"
include "cfv.mm"
include "nnre.mm"
include "ad2antrr.mm"
include "1red.mm"
include "rehalfcld.mm"
include "readdcld.mm"
include "simplr.mm"
include "remulcld.mm"
include "resincld.mm"
include "2re.mm"
include "a1i.mm"
include "pire.mm"
include "wne.mm"
include "2cnd.mm"
include "cc.mm"
include "picn.mm"
include "mulcld.mm"
include "recn.mm"
include "adantr.mm"
include "halfcld.mm"
include "sincld.mm"
include "2ne0.mm"
include "0re.mm"
include "pipos.mm"
include "gtneii.mm"
include "mulne0d.mm"
include "cz.mm"
include "divdiv1d.mm"
include "simpr.mm"
include "wb.mm"
include "crp.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcl.mm"
include "mp2an.mm"
include "mod0.mm"
include "mpan2.mm"
include "mtbid.mm"
include "eqneltrd.mm"
include "sineq0.mm"
include "syl.mm"
include "mtbird.mm"
include "neqned.mm"
include "adantll.mm"
include "redivcld.mm"

theorem dirker2re
  let cS: class S
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( N e. NN /\ S e. RR ) /\ -. ( S mod ( 2 x. _pi ) ) = 0 ) -> ( ( sin ` ( ( N + ( 1 / 2 ) ) x. S ) ) / ( ( 2 x. _pi ) x. ( sin ` ( S / 2 ) ) ) ) e. RR )

  proof
    cN
    cn
    wcel
    #
    cS
    cr
    wcel
    #
    wa
    cS
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    cc0
    wceq
    #
    wn
    #
    wa
    #
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cS
    cmul
    co
    #
    csin
    cfv
    @2
    cS
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    @5
    @8
    @5
    @7
    cS
    @5
    cN
    @6
    @0
    cN
    cr
    wcel
    @1
    @4
    cN
    nnre
    ad2antrr
    @5
    c1
    @5
    1red
    rehalfcld
    readdcld
    @0
    @1
    @4
    simplr
    #
    remulcld
    resincld
    @5
    @2
    @10
    @5
    c2
    cpi
    c2
    cr
    wcel
    @5
    2re
    a1i
    cpi
    cr
    wcel
    @5
    pire
    a1i
    remulcld
    @5
    @9
    @5
    cS
    @12
    rehalfcld
    resincld
    remulcld
    @1
    @4
    @11
    cc0
    wne
    @0
    @1
    @4
    wa
    #
    @2
    @10
    @13
    c2
    cpi
    @13
    2cnd
    #
    cpi
    cc
    wcel
    @13
    picn
    a1i
    #
    mulcld
    @13
    @9
    @13
    cS
    @1
    cS
    cc
    wcel
    @4
    cS
    recn
    adantr
    #
    halfcld
    #
    sincld
    @13
    c2
    cpi
    @14
    @15
    c2
    cc0
    wne
    @13
    2ne0
    a1i
    #
    cpi
    cc0
    wne
    @13
    cc0
    cpi
    0re
    pipos
    gtneii
    a1i
    #
    mulne0d
    @13
    @10
    cc0
    @13
    @10
    cc0
    wceq
    #
    @9
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    @13
    @21
    cS
    @2
    cdiv
    co
    #
    cz
    @13
    cS
    c2
    cpi
    @16
    @14
    @15
    @18
    @19
    divdiv1d
    @13
    @3
    @23
    cz
    wcel
    #
    @1
    @4
    simpr
    @1
    @3
    @24
    wb
    #
    @4
    @1
    @2
    crp
    wcel
    #
    @25
    c2
    crp
    wcel
    cpi
    crp
    wcel
    @26
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    cS
    @2
    mod0
    mpan2
    adantr
    mtbid
    eqneltrd
    @13
    @9
    cc
    wcel
    @20
    @22
    wb
    @17
    @9
    sineq0
    syl
    mtbird
    neqned
    mulne0d
    adantll
    redivcld
end
