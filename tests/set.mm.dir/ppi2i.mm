include "cppi.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "wn.mm"
include "wceq.mm"
include "nn0zi.mm"
include "eleq1i.mm"
include "mtbi.mm"
include "ppinprm.mm"
include "mp2an.mm"
include "3eqtri.mm"

theorem ppi2i
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vp: setvar p
  assume ppi1i.m: |- M e. NN0
  assume ppi1i.n: |- N = ( M + 1 )
  assume ppi1i.p: |- ( ppi ` M ) = K
  assume ppi2i.1: |- -. N e. Prime


  assert |- ( ppi ` N ) = K

  proof
    cN
    cppi
    cfv
    cM
    c1
    caddc
    co
    #
    cppi
    cfv
    #
    cM
    cppi
    cfv
    #
    cK
    cN
    @0
    cppi
    ppi1i.n
    fveq2i
    cM
    cz
    wcel
    @0
    cprime
    wcel
    #
    wn
    @1
    @2
    wceq
    cM
    ppi1i.m
    nn0zi
    cN
    cprime
    wcel
    @3
    ppi2i.1
    cN
    @0
    cprime
    ppi1i.n
    eleq1i
    mtbi
    cM
    ppinprm
    mp2an
    ppi1i.p
    3eqtri
end
