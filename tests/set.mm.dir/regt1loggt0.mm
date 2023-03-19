include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "clog.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cxr.mm"
include "wa.mm"
include "wb.mm"
include "1re.mm"
include "rexri.mm"
include "elioopnf.mm"
include "ax-mp.mm"
include "simprbi.mm"
include "wceq.mm"
include "log1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "breq1d.mm"
include "crp.mm"
include "1rp.mm"
include "0lt1.mm"
include "wi.mm"
include "0red.mm"
include "1red.mm"
include "id.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "imdistani.mm"
include "elrp.mm"
include "3imtr4i.mm"
include "logltb.mm"
include "sylancr.mm"
include "bitr4d.mm"
include "mpbird.mm"

theorem regt1loggt0
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( B e. ( 1 (,) +oo ) -> 0 < ( log ` B ) )

  proof
    cB
    c1
    cpnf
    cioo
    co
    wcel
    #
    cc0
    cB
    clog
    cfv
    #
    clt
    wbr
    #
    c1
    cB
    clt
    wbr
    #
    @0
    cB
    cr
    wcel
    #
    @3
    c1
    cxr
    wcel
    @0
    @4
    @3
    wa
    #
    wb
    c1
    1re
    rexri
    c1
    cB
    elioopnf
    ax-mp
    #
    simprbi
    @0
    @2
    c1
    clog
    cfv
    #
    @1
    clt
    wbr
    #
    @3
    @0
    cc0
    @7
    @1
    clt
    cc0
    @7
    wceq
    @0
    @7
    cc0
    log1
    eqcomi
    a1i
    breq1d
    @0
    c1
    crp
    wcel
    cB
    crp
    wcel
    #
    @3
    @8
    wb
    1rp
    @5
    @4
    cc0
    cB
    clt
    wbr
    #
    wa
    @0
    @9
    @4
    @3
    @10
    @4
    cc0
    c1
    clt
    wbr
    #
    @3
    @10
    0lt1
    @4
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @4
    @11
    @3
    wa
    @10
    wi
    @4
    0red
    @4
    1red
    @4
    id
    cc0
    c1
    cB
    lttr
    syl3anc
    mpani
    imdistani
    @6
    cB
    elrp
    3imtr4i
    c1
    cB
    logltb
    sylancr
    bitr4d
    mpbird
end
