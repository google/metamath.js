include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "zre.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "redivcld.mm"
include "3adant3.mm"
include "wb.mm"
include "simprl.mm"
include "simpl.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "notbid.mm"
include "biimp3a.mm"
include "flltnz.mm"
include "syl2anc.mm"

theorem fldivndvdslt
  let cK: class K
  let cL: class L


  assert |- ( ( K e. ZZ /\ ( L e. ZZ /\ L =/= 0 ) /\ -. L || K ) -> ( |_ ` ( K / L ) ) < ( K / L ) )

  proof
    cK
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    cL
    cc0
    wne
    #
    wa
    #
    cL
    cK
    cdvds
    wbr
    #
    wn
    #
    w3a
    cK
    cL
    cdiv
    co
    #
    cr
    wcel
    #
    @6
    cz
    wcel
    #
    wn
    #
    @6
    cfl
    cfv
    @6
    clt
    wbr
    @0
    @3
    @7
    @5
    @0
    @3
    wa
    #
    cK
    cL
    @0
    cK
    cr
    wcel
    @3
    cK
    zre
    adantr
    @1
    cL
    cr
    wcel
    @0
    @2
    cL
    zre
    ad2antrl
    @0
    @1
    @2
    simprr
    #
    redivcld
    3adant3
    @0
    @3
    @5
    @9
    @10
    @4
    @8
    @10
    @1
    @2
    @0
    @4
    @8
    wb
    @0
    @1
    @2
    simprl
    @11
    @0
    @3
    simpl
    cL
    cK
    dvdsval2
    syl3anc
    notbid
    biimp3a
    @6
    flltnz
    syl2anc
end
