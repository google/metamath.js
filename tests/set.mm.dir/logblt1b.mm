include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "clogb.mm"
include "co.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "clog.mm"
include "cdiv.mm"
include "relogbval.mm"
include "breq1d.mm"
include "cmul.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "relogcl.mm"
include "adantl.mm"
include "1red.mm"
include "eluz2nn.mm"
include "nnrpd.mm"
include "syl.mm"
include "eluz2gt1.mm"
include "loggt0b.mm"
include "mpbird.mm"
include "jca.mm"
include "adantr.mm"
include "ltdivmul.mm"
include "syl3anc.mm"
include "wceq.mm"
include "recnd.mm"
include "mulid1d.mm"
include "breq2d.mm"
include "anim2i.mm"
include "ancoms.mm"
include "logltb.mm"
include "bicomd.mm"
include "bitrd.mm"

theorem logblt1b
  let cB: class B
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ ) -> ( ( B logb X ) < 1 <-> X < B ) )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cX
    crp
    wcel
    #
    wa
    #
    cB
    cX
    clogb
    co
    #
    c1
    clt
    wbr
    cX
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    c1
    clt
    wbr
    #
    cX
    cB
    clt
    wbr
    #
    @2
    @3
    @6
    c1
    clt
    cB
    cX
    relogbval
    breq1d
    @2
    @7
    @4
    @5
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @8
    @2
    @4
    cr
    wcel
    #
    c1
    cr
    wcel
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
    #
    @7
    @10
    wb
    @1
    @11
    @0
    cX
    relogcl
    adantl
    @2
    1red
    @0
    @14
    @1
    @0
    @12
    @13
    @0
    cB
    crp
    wcel
    #
    @12
    @0
    cB
    cB
    eluz2nn
    nnrpd
    #
    cB
    relogcl
    syl
    #
    @0
    @13
    c1
    cB
    clt
    wbr
    #
    cB
    eluz2gt1
    @0
    @15
    @13
    @18
    wb
    @16
    cB
    loggt0b
    syl
    mpbird
    jca
    adantr
    @4
    c1
    @5
    ltdivmul
    syl3anc
    @2
    @10
    @4
    @5
    clt
    wbr
    #
    @8
    @2
    @9
    @5
    @4
    clt
    @0
    @9
    @5
    wceq
    @1
    @0
    @5
    @0
    @5
    @17
    recnd
    mulid1d
    adantr
    breq2d
    @2
    @1
    @15
    wa
    #
    @19
    @8
    wb
    @1
    @0
    @20
    @0
    @15
    @1
    @16
    anim2i
    ancoms
    @20
    @8
    @19
    cX
    cB
    logltb
    bicomd
    syl
    bitrd
    bitrd
    bitrd
end
