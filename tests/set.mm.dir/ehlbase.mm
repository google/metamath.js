include "cn0.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "crrx.mm"
include "cr.mm"
include "cmap.mm"
include "ehlval.mm"
include "fveq2d.mm"
include "cv.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "rabid2.mm"
include "elmapi.mm"
include "fzfid.mm"
include "0red.mm"
include "fdmfifsupp.mm"
include "mprgbir.mm"
include "cvv.mm"
include "ovex.mm"
include "eqid.mm"
include "rrxbase.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "syl6reqr.mm"

theorem ehlbase
  let cE: class E
  let cN: class N
  let vf: setvar f
  let vn: setvar n
  assume ehlval.e: |- E = ( EEhil ` N )


  assert |- ( N e. NN0 -> ( RR ^m ( 1 ... N ) ) = ( Base ` E ) )

  proof
    cN
    cn0
    wcel
    #
    cE
    cbs
    cfv
    c1
    cN
    cfz
    co
    #
    crrx
    cfv
    #
    cbs
    cfv
    #
    cr
    @1
    cmap
    co
    #
    @0
    cE
    @2
    cbs
    cE
    cN
    ehlval.e
    ehlval
    fveq2d
    @4
    vf
    cv
    #
    cc0
    cfsupp
    wbr
    #
    vf
    @4
    crab
    #
    @3
    @4
    @7
    wceq
    @6
    vf
    @4
    @6
    vf
    @4
    rabid2
    @5
    @4
    wcel
    #
    @1
    cr
    @5
    cr
    cc0
    @5
    cr
    @1
    elmapi
    @8
    c1
    cN
    fzfid
    @8
    0red
    fdmfifsupp
    mprgbir
    @1
    cvv
    wcel
    @3
    @7
    wceq
    c1
    cN
    cfz
    ovex
    @3
    vf
    @2
    @1
    cvv
    @2
    eqid
    @3
    eqid
    rrxbase
    ax-mp
    eqtr4i
    syl6reqr
end
