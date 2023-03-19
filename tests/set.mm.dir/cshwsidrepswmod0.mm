include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cprime.mm"
include "cz.mm"
include "w3a.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cmo.mm"
include "cc0.mm"
include "creps.mm"
include "wo.mm"
include "wi.mm"
include "orc.mm"
include "2a1d.mm"
include "wne.mm"
include "wa.mm"
include "3simpa.mm"
include "ad2antlr.mm"
include "simplr3.mm"
include "simpll.mm"
include "simpr.mm"
include "cshwsidrepsw.mm"
include "imp.mm"
include "syl13anc.mm"
include "olcd.mm"
include "exp31.mm"
include "pm2.61ine.mm"

theorem cshwsidrepswmod0
  let cL: class L
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ ( # ` W ) e. Prime /\ L e. ZZ ) -> ( ( W cyclShift L ) = W -> ( ( L mod ( # ` W ) ) = 0 \/ W = ( ( W ` 0 ) repeatS ( # ` W ) ) ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    cprime
    wcel
    #
    cL
    cz
    wcel
    #
    w3a
    #
    cW
    cL
    ccsh
    co
    cW
    wceq
    #
    cL
    @1
    cmo
    co
    #
    cc0
    wceq
    #
    cW
    cc0
    cW
    cfv
    @1
    creps
    co
    wceq
    #
    wo
    #
    wi
    wi
    @6
    cc0
    @7
    @9
    @4
    @5
    @7
    @8
    orc
    2a1d
    @6
    cc0
    wne
    #
    @4
    @5
    @9
    @10
    @4
    wa
    #
    @5
    wa
    #
    @8
    @7
    @12
    @0
    @2
    wa
    #
    @3
    @10
    @5
    @8
    @4
    @13
    @10
    @5
    @0
    @2
    @3
    3simpa
    ad2antlr
    @0
    @2
    @3
    @10
    @5
    simplr3
    @10
    @4
    @5
    simpll
    @11
    @5
    simpr
    @13
    @3
    @10
    @5
    w3a
    @8
    cL
    cV
    cW
    cshwsidrepsw
    imp
    syl13anc
    olcd
    exp31
    pm2.61ine
end
