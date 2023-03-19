include "ctop.mm"
include "wcel.mm"
include "wceq.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "cnei.mm"
include "cfv.mm"
include "cv.mm"
include "cnt.mm"
include "simpl2.mm"
include "simprl.mm"
include "simpl1.mm"
include "simprr.mm"
include "neii1.mm"
include "syl2anc.mm"
include "ntropn.mm"
include "sseldd.mm"
include "wb.mm"
include "neiss2.mm"
include "neiint.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "opnneiss.mm"
include "ntrss2.mm"
include "simpl3.mm"
include "sseqtrd.mm"
include "ssnei2.mm"
include "syl22anc.mm"
include "expr.mm"
include "ssrdv.mm"

theorem topssnei
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vn: setvar n
  let cP: class P
  assume tpnei.1: |- X = U. J
  assume topssnei.2: |- Y = U. K


  assert |- ( ( ( J e. Top /\ K e. Top /\ X = Y ) /\ J C_ K ) -> ( ( nei ` J ) ` S ) C_ ( ( nei ` K ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cX
    cY
    wceq
    #
    w3a
    #
    cJ
    cK
    wss
    #
    wa
    vx
    cS
    cJ
    cnei
    cfv
    cfv
    #
    cS
    cK
    cnei
    cfv
    cfv
    #
    @3
    @4
    vx
    cv
    #
    @5
    wcel
    #
    @7
    @6
    wcel
    #
    @3
    @4
    @8
    wa
    #
    wa
    #
    @1
    @7
    cJ
    cnt
    cfv
    cfv
    #
    @6
    wcel
    #
    @12
    @7
    wss
    #
    @7
    cY
    wss
    @9
    @0
    @1
    @2
    @10
    simpl2
    #
    @11
    @1
    @12
    cK
    wcel
    cS
    @12
    wss
    #
    @13
    @15
    @11
    cJ
    cK
    @12
    @3
    @4
    @8
    simprl
    @11
    @0
    @7
    cX
    wss
    #
    @12
    cJ
    wcel
    @0
    @1
    @2
    @10
    simpl1
    #
    @11
    @0
    @8
    @17
    @18
    @3
    @4
    @8
    simprr
    #
    cS
    cJ
    @7
    cX
    tpnei.1
    neii1
    syl2anc
    #
    @7
    cJ
    cX
    tpnei.1
    ntropn
    syl2anc
    sseldd
    @11
    @8
    @16
    @19
    @11
    @0
    cS
    cX
    wss
    #
    @17
    @8
    @16
    wb
    @18
    @11
    @0
    @8
    @21
    @18
    @19
    cS
    cJ
    @7
    cX
    tpnei.1
    neiss2
    syl2anc
    @20
    cS
    cJ
    @7
    cX
    tpnei.1
    neiint
    syl3anc
    mpbid
    cS
    cK
    @12
    opnneiss
    syl3anc
    @11
    @0
    @17
    @14
    @18
    @20
    @7
    cJ
    cX
    tpnei.1
    ntrss2
    syl2anc
    @11
    @7
    cX
    cY
    @20
    @0
    @1
    @2
    @10
    simpl3
    sseqtrd
    cS
    cK
    @7
    @12
    cY
    topssnei.2
    ssnei2
    syl22anc
    expr
    ssrdv
end
