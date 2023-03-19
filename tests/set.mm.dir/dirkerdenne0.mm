include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "2cnd.mm"
include "cc.mm"
include "picn.mm"
include "a1i.mm"
include "mulcld.mm"
include "recn.mm"
include "adantr.mm"
include "halfcld.mm"
include "sincld.mm"
include "wne.mm"
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

theorem dirkerdenne0
  let cS: class S
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. RR /\ -. ( S mod ( 2 x. _pi ) ) = 0 ) -> ( ( 2 x. _pi ) x. ( sin ` ( S / 2 ) ) ) =/= 0 )

  proof
    cS
    cr
    wcel
    #
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
    @1
    cS
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    @4
    c2
    cpi
    @4
    2cnd
    #
    cpi
    cc
    wcel
    @4
    picn
    a1i
    #
    mulcld
    @4
    @5
    @4
    cS
    @0
    cS
    cc
    wcel
    @3
    cS
    recn
    adantr
    #
    halfcld
    #
    sincld
    @4
    c2
    cpi
    @7
    @8
    c2
    cc0
    wne
    @4
    2ne0
    a1i
    #
    cpi
    cc0
    wne
    @4
    cc0
    cpi
    0re
    pipos
    gtneii
    a1i
    #
    mulne0d
    @4
    @6
    cc0
    @4
    @6
    cc0
    wceq
    #
    @5
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    @4
    @14
    cS
    @1
    cdiv
    co
    #
    cz
    @4
    cS
    c2
    cpi
    @9
    @7
    @8
    @11
    @12
    divdiv1d
    @4
    @2
    @16
    cz
    wcel
    #
    @0
    @3
    simpr
    @0
    @2
    @17
    wb
    #
    @3
    @0
    @1
    crp
    wcel
    #
    @18
    c2
    crp
    wcel
    cpi
    crp
    wcel
    @19
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    cS
    @1
    mod0
    mpan2
    adantr
    mtbid
    eqneltrd
    @4
    @5
    cc
    wcel
    @13
    @15
    wb
    @10
    @5
    sineq0
    syl
    mtbird
    neqned
    mulne0d
end
