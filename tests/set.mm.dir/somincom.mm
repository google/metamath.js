include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cif.mm"
include "wn.mm"
include "wi.mm"
include "so2nr.mm"
include "nan.mm"
include "mpbi.mm"
include "iffalsed.mm"
include "eqcomd.mm"
include "wceq.mm"
include "wo.mm"
include "sotric.mm"
include "con2bid.mm"
include "ifeq2.mm"
include "ifid.mm"
include "syl6req.mm"
include "iftrue.mm"
include "jaoi.mm"
include "syl6bir.mm"
include "imp.mm"
include "ifeqda.mm"

theorem somincom
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) -> if ( A R B , A , B ) = if ( B R A , B , A ) )

  proof
    cX
    cR
    wor
    cA
    cX
    wcel
    cB
    cX
    wcel
    wa
    wa
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cB
    cA
    cR
    wbr
    #
    cB
    cA
    cif
    #
    @0
    @1
    wa
    #
    @3
    cA
    @4
    @2
    cB
    cA
    @0
    @1
    @2
    wa
    wn
    wi
    @4
    @2
    wn
    wi
    cX
    cA
    cB
    cR
    so2nr
    @0
    @1
    @2
    nan
    mpbi
    iffalsed
    eqcomd
    @0
    @1
    wn
    #
    cB
    @3
    wceq
    #
    @0
    @5
    cA
    cB
    wceq
    #
    @2
    wo
    #
    @6
    @0
    @1
    @8
    cX
    cA
    cB
    cR
    sotric
    con2bid
    @7
    @6
    @2
    @7
    @3
    @2
    cB
    cB
    cif
    cB
    @2
    cA
    cB
    cB
    ifeq2
    @2
    cB
    ifid
    syl6req
    @2
    @3
    cB
    @2
    cB
    cA
    iftrue
    eqcomd
    jaoi
    syl6bir
    imp
    ifeqda
end
