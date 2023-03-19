include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "crab.mm"
include "wceq.mm"
include "rabid2.mm"
include "wss.mm"
include "c0.mm"
include "csn.mm"
include "df1o2.mm"
include "snfi.mm"
include "eqeltri.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "elmapi.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ssfi.mm"
include "sylancr.mm"
include "mprgbir.mm"

theorem psr1baslem
  let vf: setvar f


  assert |- ( NN0 ^m 1o ) = { f e. ( NN0 ^m 1o ) | ( `' f " NN ) e. Fin }

  proof
    cn0
    c1o
    cmap
    co
    #
    vf
    cv
    #
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    vf
    @0
    crab
    wceq
    @3
    vf
    @0
    @3
    vf
    @0
    rabid2
    @1
    @0
    wcel
    #
    c1o
    cfn
    wcel
    @2
    c1o
    wss
    @3
    c1o
    c0
    csn
    cfn
    df1o2
    c0
    snfi
    eqeltri
    @4
    @1
    cdm
    #
    @2
    c1o
    @1
    cn
    cnvimass
    @4
    c1o
    cn0
    @1
    wf
    @5
    c1o
    wceq
    @1
    cn0
    c1o
    elmapi
    c1o
    cn0
    @1
    fdm
    syl
    syl5sseq
    c1o
    @2
    ssfi
    sylancr
    mprgbir
end
