include "cseq.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt2.mm"
include "crdg.mm"
include "com.mm"
include "cima.mm"
include "df-seq.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "nfop.mm"
include "nfmpt2.mm"
include "nfrdg.mm"
include "nfima.mm"
include "nfcxfr.mm"

theorem nfseq
  let vx: setvar x
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let vw: setvar w
  let vz: setvar z
  assume nfseq.1: |- F/_ x M
  assume nfseq.2: |- F/_ x .+
  assume nfseq.3: |- F/_ x F


  assert |- F/_ x seq M ( .+ , F )

  proof
    vx
    c.pl
    cF
    cM
    cseq
    vz
    vw
    cvv
    cvv
    vz
    cv
    c1
    caddc
    co
    #
    vw
    cv
    #
    @0
    cF
    cfv
    #
    c.pl
    co
    #
    cop
    #
    cmpt2
    #
    cM
    cM
    cF
    cfv
    #
    cop
    #
    crdg
    #
    com
    cima
    vz
    vw
    c.pl
    cF
    cM
    df-seq
    vx
    @8
    com
    vx
    @7
    @5
    vz
    vw
    vx
    cvv
    cvv
    @4
    vx
    cvv
    nfcv
    #
    @9
    vx
    @0
    @3
    vx
    @0
    nfcv
    #
    vx
    @1
    @2
    c.pl
    vx
    @1
    nfcv
    nfseq.2
    vx
    @0
    cF
    nfseq.3
    @10
    nffv
    nfov
    nfop
    nfmpt2
    vx
    cM
    @6
    nfseq.1
    vx
    cM
    cF
    nfseq.3
    nfseq.1
    nffv
    nfop
    nfrdg
    vx
    com
    nfcv
    nfima
    nfcxfr
end
