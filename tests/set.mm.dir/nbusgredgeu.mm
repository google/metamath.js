include "cusgr.mm"
include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "nbusgreledg.mm"
include "biimpa.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "rmoeq.mm"
include "a1i.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem nbusgredgeu
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  assume nbusgredgeu.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint M e
  disjoint N e
  assert |- ( ( G e. USGraph /\ M e. ( G NeighbVtx N ) ) -> E! e e. E e = { M , N } )

  proof
    cG
    cusgr
    wcel
    #
    cM
    cG
    cN
    cnbgr
    co
    wcel
    #
    wa
    #
    ve
    cv
    #
    cM
    cN
    cpr
    #
    wceq
    #
    ve
    cE
    wrex
    @5
    ve
    cE
    wrmo
    #
    @5
    ve
    cE
    wreu
    @2
    @5
    @4
    @4
    wceq
    #
    ve
    @4
    cE
    @0
    @1
    @4
    cE
    wcel
    cE
    cG
    cN
    cM
    nbusgredgeu.e
    nbusgreledg
    biimpa
    @5
    @5
    @7
    wb
    @2
    @3
    @4
    @4
    eqeq1
    adantl
    @2
    @4
    eqidd
    rspcedvd
    @6
    @2
    ve
    @4
    cE
    rmoeq
    a1i
    @5
    ve
    cE
    reu5
    sylanbrc
end
