include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cico.mm"
include "cc0.mm"
include "clogb.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "w3a.mm"
include "cr.mm"
include "clt.mm"
include "wa.mm"
include "zre.mm"
include "3ad2ant2.mm"
include "1lt2.mm"
include "wi.mm"
include "1re.mm"
include "a1i.mm"
include "2re.mm"
include "adantl.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "3impia.mm"
include "jca.mm"
include "eluz2.mm"
include "cxr.mm"
include "wb.mm"
include "rexri.mm"
include "elioopnf.mm"
include "ax-mp.mm"
include "3imtr4i.mm"
include "rege1logbrege0.mm"
include "sylan.mm"

theorem rege1logbzge0
  let cB: class B
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. ( 1 [,) +oo ) ) -> 0 <_ ( B logb X ) )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cB
    c1
    cpnf
    cioo
    co
    wcel
    #
    cX
    c1
    cpnf
    cico
    co
    wcel
    cc0
    cB
    cX
    clogb
    co
    cle
    wbr
    c2
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    c2
    cB
    cle
    wbr
    #
    w3a
    #
    cB
    cr
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    wa
    #
    @0
    @1
    @5
    @6
    @7
    @3
    @2
    @6
    @4
    cB
    zre
    #
    3ad2ant2
    @2
    @3
    @4
    @7
    @2
    @3
    wa
    #
    c1
    c2
    clt
    wbr
    #
    @4
    @7
    1lt2
    @10
    c1
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @6
    @11
    @4
    wa
    @7
    wi
    @12
    @10
    1re
    a1i
    @13
    @10
    2re
    a1i
    @3
    @6
    @2
    @9
    adantl
    c1
    c2
    cB
    ltletr
    syl3anc
    mpani
    3impia
    jca
    c2
    cB
    eluz2
    c1
    cxr
    wcel
    @1
    @8
    wb
    c1
    1re
    rexri
    c1
    cB
    elioopnf
    ax-mp
    3imtr4i
    cB
    cX
    rege1logbrege0
    sylan
end
