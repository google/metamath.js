include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "trclfv.mm"
include "breqd.mm"
include "cop.mm"
include "brintclab.mm"
include "df-br.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem brtrclfv
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let vr: setvar r

  disjoint A r
  disjoint B r
  disjoint R r
  assert |- ( R e. V -> ( A ( t+ ` R ) B <-> A. r ( ( R C_ r /\ ( r o. r ) C_ r ) -> A r B ) ) )

  proof
    cR
    cV
    wcel
    #
    cA
    cB
    cR
    ctcl
    cfv
    #
    wbr
    cA
    cB
    cR
    vr
    cv
    #
    wss
    @2
    @2
    ccom
    @2
    wss
    wa
    #
    vr
    cab
    cint
    #
    wbr
    #
    @3
    cA
    cB
    @2
    wbr
    #
    wi
    #
    vr
    wal
    #
    @0
    @1
    @4
    cA
    cB
    vr
    cR
    cV
    trclfv
    breqd
    @5
    @3
    cA
    cB
    cop
    @2
    wcel
    #
    wi
    #
    vr
    wal
    @8
    @3
    vr
    cA
    cB
    brintclab
    @7
    @10
    vr
    @6
    @9
    @3
    cA
    cB
    @2
    df-br
    imbi2i
    albii
    bitr4i
    syl6bb
end
