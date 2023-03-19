include "wcel.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cn0.mm"
include "cmap.mm"
include "eqid.mm"
include "psr1baslem.mm"
include "id.mm"
include "cps1.mm"
include "ply1bas.mm"
include "syl6eleq.mm"
include "mplelf.mm"

theorem ply1basf
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cK: class K
  let va: setvar a
  assume ply1rcl.p: |- P = ( Poly1 ` R )
  assume ply1rcl.b: |- B = ( Base ` P )
  assume ply1basf.k: |- K = ( Base ` R )


  assert |- ( F e. B -> F : ( NN0 ^m 1o ) --> K )

  proof
    cF
    cB
    wcel
    #
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    cn0
    c1o
    cmap
    co
    @1
    cR
    va
    c1o
    cK
    cF
    @1
    eqid
    ply1basf.k
    @2
    eqid
    va
    psr1baslem
    @0
    cF
    cB
    @2
    @0
    id
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    ply1rcl.p
    @3
    eqid
    ply1rcl.b
    ply1bas
    syl6eleq
    mplelf
end
