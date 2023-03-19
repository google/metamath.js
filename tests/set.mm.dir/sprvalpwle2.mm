include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "sprvalpwn0.mm"
include "wa.mm"
include "wb.mm"
include "hashle2prv.mm"
include "adantl.mm"
include "bicomd.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem sprvalpwle2
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x

  disjoint V p
  disjoint W p
  disjoint V a
  disjoint V b
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint W a
  disjoint W b
  disjoint k x
  assert |- ( V e. W -> ( Pairs ` V ) = { p e. ( ~P V \ { (/) } ) | ( # ` p ) <_ 2 } )

  proof
    cV
    cW
    wcel
    #
    cV
    cspr
    cfv
    vp
    cv
    #
    va
    cv
    vb
    cv
    cpr
    wceq
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    vp
    cV
    cpw
    c0
    csn
    cdif
    #
    crab
    @1
    chash
    cfv
    c2
    cle
    wbr
    #
    vp
    @3
    crab
    cV
    cW
    vp
    va
    vb
    sprvalpwn0
    @0
    @2
    @4
    vp
    @3
    @0
    @1
    @3
    wcel
    #
    wa
    @4
    @2
    @5
    @4
    @2
    wb
    @0
    @1
    cV
    va
    vb
    hashle2prv
    adantl
    bicomd
    rabbidva
    eqtrd
end
