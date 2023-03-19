include "crg.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "wss.mm"
include "cur.mm"
include "cfv.mm"
include "csubrg.mm"
include "ressid.mm"
include "id.mm"
include "eqeltrd.mm"
include "ancli.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ssid.mm"
include "jctil.mm"
include "issubrg.mm"
include "sylanbrc.mm"

theorem subrgid
  let cB: class B
  let cR: class R
  assume subrgss.1: |- B = ( Base ` R )


  assert |- ( R e. Ring -> B e. ( SubRing ` R ) )

  proof
    cR
    crg
    wcel
    #
    @0
    cR
    cB
    cress
    co
    #
    crg
    wcel
    #
    wa
    cB
    cB
    wss
    #
    cR
    cur
    cfv
    #
    cB
    wcel
    #
    wa
    cB
    cR
    csubrg
    cfv
    wcel
    @0
    @2
    @0
    @1
    cR
    crg
    cB
    cR
    crg
    subrgss.1
    ressid
    @0
    id
    eqeltrd
    ancli
    @0
    @5
    @3
    cB
    cR
    @4
    subrgss.1
    @4
    eqid
    #
    ringidcl
    cB
    ssid
    jctil
    cB
    cB
    cR
    @4
    subrgss.1
    @6
    issubrg
    sylanbrc
end
