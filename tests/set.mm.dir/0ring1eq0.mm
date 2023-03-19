include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "eldif.mm"
include "cbs.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "0ringnnzr.mm"
include "eqid.mm"
include "0ring01eq.mm"
include "eqcomd.mm"
include "ex.mm"
include "sylbird.mm"
include "imp.mm"
include "sylbi.mm"

theorem 0ring1eq0
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  let vk: setvar k
  let vx: setvar x
  assume 0ringdif.b: |- B = ( Base ` R )
  assume 0ringdif.0: |- .0. = ( 0g ` R )
  assume 0ring1eq0.1: |- .1. = ( 1r ` R )


  assert |- ( R e. ( Ring \ NzRing ) -> .1. = .0. )

  proof
    cR
    crg
    cnzr
    cdif
    wcel
    cR
    crg
    wcel
    #
    cR
    cnzr
    wcel
    wn
    #
    wa
    c.1
    c.0
    wceq
    #
    cR
    crg
    cnzr
    eldif
    @0
    @1
    @2
    @0
    @1
    cR
    cbs
    cfv
    #
    chash
    cfv
    c1
    wceq
    #
    @2
    cR
    0ringnnzr
    @0
    @4
    @2
    @0
    @4
    wa
    c.0
    c.1
    @3
    cR
    c.1
    c.0
    @3
    eqid
    0ringdif.0
    0ring1eq0.1
    0ring01eq
    eqcomd
    ex
    sylbird
    imp
    sylbi
end
