include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "catan.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "ctan.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wb.mm"
include "atanbnd.mm"
include "tanord.mm"
include "syl2an.mm"
include "cdm.mm"
include "wceq.mm"
include "atanre.mm"
include "tanatan.mm"
include "syl.mm"
include "breqan12d.mm"
include "bitr2d.mm"

theorem atanord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> ( arctan ` A ) < ( arctan ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    catan
    cfv
    #
    cB
    catan
    cfv
    #
    clt
    wbr
    #
    @2
    ctan
    cfv
    #
    @3
    ctan
    cfv
    #
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    @0
    @2
    cpi
    c2
    cdiv
    co
    #
    cneg
    @8
    cioo
    co
    #
    wcel
    @3
    @9
    wcel
    @4
    @7
    wb
    @1
    cA
    atanbnd
    cB
    atanbnd
    @2
    @3
    tanord
    syl2an
    @0
    @1
    @5
    cA
    @6
    cB
    clt
    @0
    cA
    catan
    cdm
    #
    wcel
    @5
    cA
    wceq
    cA
    atanre
    cA
    tanatan
    syl
    @1
    cB
    @10
    wcel
    @6
    cB
    wceq
    cB
    atanre
    cB
    tanatan
    syl
    breqan12d
    bitr2d
end
