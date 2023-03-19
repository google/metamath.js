include "crp.mm"
include "wcel.mm"
include "c2.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "clt.mm"
include "wa.mm"
include "cz.mm"
include "cuz.mm"
include "2z.mm"
include "uzid.mm"
include "mp1i.mm"
include "id.mm"
include "eqid.mm"
include "fllogbd.mm"
include "cr.mm"
include "wb.mm"
include "2re.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "relogbzcl.mm"
include "syl2anc.mm"
include "flcld.mm"
include "reexpclzd.mm"
include "2pos.mm"
include "expgt0.mm"
include "syl3anc.mm"
include "elrpd.mm"
include "rpre.mm"
include "divge1b.mm"
include "bicomd.mm"
include "biimprd.mm"
include "cmul.mm"
include "2cnd.mm"
include "expp1zd.mm"
include "breq2d.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "1p1e2.mm"
include "breq2i.mm"
include "syl6ibr.mm"
include "anim12d.mm"
include "mpd.mm"
include "expne0d.mm"
include "redivcld.mm"
include "1zzd.mm"
include "flbi.mm"
include "mpbird.mm"

theorem fldivexpfllog2
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( X e. RR+ -> ( |_ ` ( X / ( 2 ^ ( |_ ` ( 2 logb X ) ) ) ) ) = 1 )

  proof
    cX
    crp
    wcel
    #
    cX
    c2
    c2
    cX
    clogb
    co
    #
    cfl
    cfv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    c1
    wceq
    #
    c1
    @4
    cle
    wbr
    #
    @4
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @0
    @3
    cX
    cle
    wbr
    #
    cX
    c2
    @2
    c1
    caddc
    co
    cexp
    co
    #
    clt
    wbr
    #
    wa
    @9
    @0
    c2
    @2
    cX
    c2
    cz
    wcel
    c2
    c2
    cuz
    cfv
    wcel
    #
    @0
    2z
    c2
    uzid
    mp1i
    #
    @0
    id
    #
    @2
    eqid
    fllogbd
    @0
    @10
    @6
    @12
    @8
    @0
    @6
    @10
    @0
    @3
    crp
    wcel
    #
    cX
    cr
    wcel
    #
    @6
    @10
    wb
    @0
    @3
    @0
    c2
    @2
    c2
    cr
    wcel
    #
    @0
    2re
    a1i
    #
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    #
    @0
    @1
    @0
    @13
    @0
    @1
    cr
    wcel
    @14
    @15
    c2
    cX
    relogbzcl
    syl2anc
    flcld
    #
    reexpclzd
    #
    @0
    @18
    @2
    cz
    wcel
    cc0
    c2
    clt
    wbr
    #
    cc0
    @3
    clt
    wbr
    #
    @19
    @21
    @23
    @0
    2pos
    a1i
    c2
    @2
    expgt0
    syl3anc
    #
    elrpd
    cX
    rpre
    #
    @16
    @17
    wa
    @10
    @6
    @3
    cX
    divge1b
    bicomd
    syl2anc
    biimprd
    @0
    @12
    @4
    c2
    clt
    wbr
    #
    @8
    @0
    @12
    @27
    @0
    @12
    cX
    @3
    c2
    cmul
    co
    #
    clt
    wbr
    #
    @27
    @0
    @11
    @28
    cX
    clt
    @0
    c2
    @2
    @0
    2cnd
    #
    @20
    @21
    expp1zd
    breq2d
    @0
    @17
    @18
    @3
    cr
    wcel
    @24
    @27
    @29
    wb
    @26
    @19
    @22
    @25
    cX
    c2
    @3
    ltdivmul
    syl112anc
    bitr4d
    biimpd
    @7
    c2
    @4
    clt
    1p1e2
    breq2i
    syl6ibr
    anim12d
    mpd
    @0
    @4
    cr
    wcel
    c1
    cz
    wcel
    @5
    @9
    wb
    @0
    cX
    @3
    @26
    @22
    @0
    c2
    @2
    @30
    @20
    @21
    expne0d
    redivcld
    @0
    1zzd
    @4
    c1
    flbi
    syl2anc
    mpbird
end
