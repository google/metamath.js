include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "wtru.mm"
include "cmps.mm"
include "con0.mm"
include "eqid.mm"
include "psr1baslem.mm"
include "psr1bas2.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "psrbas.mm"
include "trud.mm"

theorem psr1bas
  let cB: class B
  let cR: class R
  let cS: class S
  let cK: class K
  let vr: setvar r
  let vf: setvar f
  assume psr1val.1: |- S = ( PwSer1 ` R )
  assume psr1bas2.b: |- B = ( Base ` S )
  assume psr1bas.k: |- K = ( Base ` R )


  assert |- B = ( K ^m ( NN0 ^m 1o ) )

  proof
    cB
    cK
    cn0
    c1o
    cmap
    co
    #
    cmap
    co
    wceq
    wtru
    cB
    @0
    cR
    c1o
    cR
    cmps
    co
    #
    vf
    c1o
    cK
    con0
    @1
    eqid
    #
    psr1bas.k
    vf
    psr1baslem
    cB
    cR
    cS
    @1
    psr1val.1
    psr1bas2.b
    @2
    psr1bas2
    c1o
    con0
    wcel
    wtru
    1on
    a1i
    psrbas
    trud
end
