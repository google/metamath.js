include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cc0.mm"
include "clogb.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "cdiv.mm"
include "c1.mm"
include "relogbval.mm"
include "breq2d.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "relogcl.mm"
include "adantl.mm"
include "eluz2nn.mm"
include "nnrpd.mm"
include "syl.mm"
include "adantr.mm"
include "eluz2gt1.mm"
include "loggt0b.mm"
include "mpbird.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "logge0b.mm"
include "3bitr2d.mm"

theorem logbge0b
  let cB: class B
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ ) -> ( 0 <_ ( B logb X ) <-> 1 <_ X ) )

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
    cc0
    cB
    cX
    clogb
    co
    #
    cle
    wbr
    cc0
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
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    c1
    cX
    cle
    wbr
    #
    @2
    @3
    @6
    cc0
    cle
    cB
    cX
    relogbval
    breq2d
    @2
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    @8
    @7
    wb
    @1
    @10
    @0
    cX
    relogcl
    adantl
    @0
    @11
    @1
    @0
    cB
    crp
    wcel
    #
    @11
    @0
    cB
    cB
    eluz2nn
    nnrpd
    #
    cB
    relogcl
    syl
    adantr
    @0
    @12
    @1
    @0
    @12
    c1
    cB
    clt
    wbr
    #
    cB
    eluz2gt1
    @0
    @13
    @12
    @15
    wb
    @14
    cB
    loggt0b
    syl
    mpbird
    adantr
    @4
    @5
    ge0div
    syl3anc
    @1
    @8
    @9
    wb
    @0
    cX
    logge0b
    adantl
    3bitr2d
end
