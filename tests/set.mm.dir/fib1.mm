include "c1.mm"
include "cfib.mm"
include "cfv.mm"
include "cc0.mm"
include "cs2.mm"
include "cn0.mm"
include "cword.mm"
include "chash.mm"
include "ccnv.mm"
include "c2.mm"
include "cuz.mm"
include "cima.mm"
include "cin.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cmpt.mm"
include "csseq.mm"
include "df-fib.mm"
include "fveq1i.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "nn0ex.mm"
include "a1i.mm"
include "0nn0.mm"
include "1nn0.mm"
include "s2cld.mm"
include "eqid.mm"
include "wf.mm"
include "fiblem.mm"
include "cfzo.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "2nn.mm"
include "1lt2.mm"
include "elfzo0.mm"
include "mpbir3an.mm"
include "s2len.mm"
include "oveq2i.mm"
include "eleqtrri.mm"
include "sseqfv1.mm"
include "trud.mm"
include "s2fv1.mm"
include "ax-mp.mm"
include "3eqtri.mm"

theorem fib1
  let vw: setvar w


  assert |- ( Fibci ` 1 ) = 1

  proof
    c1
    cfib
    cfv
    c1
    cc0
    c1
    cs2
    #
    vw
    cn0
    cword
    #
    chash
    ccnv
    #
    c2
    cuz
    cfv
    cima
    cin
    vw
    cv
    #
    chash
    cfv
    #
    c2
    cmin
    co
    @3
    cfv
    @4
    c1
    cmin
    co
    @3
    cfv
    caddc
    co
    cmpt
    #
    csseq
    co
    #
    cfv
    #
    c1
    @0
    cfv
    #
    c1
    c1
    cfib
    @6
    vw
    df-fib
    fveq1i
    @7
    @8
    wceq
    wtru
    cn0
    @5
    @0
    c1
    @1
    @2
    @0
    chash
    cfv
    #
    cuz
    cfv
    cima
    cin
    #
    cn0
    cvv
    wcel
    wtru
    nn0ex
    a1i
    wtru
    cc0
    c1
    cn0
    cc0
    cn0
    wcel
    wtru
    0nn0
    a1i
    c1
    cn0
    wcel
    #
    wtru
    1nn0
    a1i
    s2cld
    @10
    eqid
    @10
    cn0
    @5
    wf
    wtru
    vw
    fiblem
    a1i
    c1
    cc0
    @9
    cfzo
    co
    #
    wcel
    wtru
    c1
    cc0
    c2
    cfzo
    co
    #
    @12
    c1
    @13
    wcel
    @11
    c2
    cn
    wcel
    c1
    c2
    clt
    wbr
    1nn0
    2nn
    1lt2
    c1
    c2
    elfzo0
    mpbir3an
    @9
    c2
    cc0
    cfzo
    cc0
    c1
    s2len
    oveq2i
    eleqtrri
    a1i
    sseqfv1
    trud
    @11
    @8
    c1
    wceq
    1nn0
    cc0
    c1
    cn0
    s2fv1
    ax-mp
    3eqtri
end
