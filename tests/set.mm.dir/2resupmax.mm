include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "cif.mm"
include "cle.mm"
include "wor.mm"
include "wceq.mm"
include "ltso.mm"
include "suppr.mm"
include "mp3an1.mm"
include "wn.mm"
include "ifnot.mm"
include "lenlt.mm"
include "bicomd.mm"
include "ifbid.mm"
include "syl5eqr.mm"
include "eqtrd.mm"

theorem 2resupmax
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> sup ( { A , B } , RR , < ) = if ( A <_ B , B , A ) )

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
    #
    cA
    cB
    cpr
    cr
    clt
    csup
    #
    cB
    cA
    clt
    wbr
    #
    cA
    cB
    cif
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cif
    #
    cr
    clt
    wor
    @0
    @1
    @3
    @5
    wceq
    ltso
    cr
    cA
    cB
    clt
    suppr
    mp3an1
    @2
    @5
    @4
    wn
    #
    cB
    cA
    cif
    @7
    @4
    cB
    cA
    ifnot
    @2
    @8
    @6
    cB
    cA
    @2
    @6
    @8
    cA
    cB
    lenlt
    bicomd
    ifbid
    syl5eqr
    eqtrd
end
