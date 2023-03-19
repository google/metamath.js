include "cppi.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "wceq.mm"
include "nn0zi.mm"
include "eqeltrri.mm"
include "ppiprm.mm"
include "mp2an.mm"
include "oveq1i.mm"
include "3eqtri.mm"

theorem ppi1i
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vp: setvar p
  assume ppi1i.m: |- M e. NN0
  assume ppi1i.n: |- N = ( M + 1 )
  assume ppi1i.p: |- ( ppi ` M ) = K
  assume ppi1i.1: |- N e. Prime


  assert |- ( ppi ` N ) = ( K + 1 )

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
    c1
    caddc
    co
    #
    cK
    c1
    caddc
    co
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
    @1
    @3
    wceq
    cM
    ppi1i.m
    nn0zi
    cN
    @0
    cprime
    ppi1i.n
    ppi1i.1
    eqeltrri
    cM
    ppiprm
    mp2an
    @2
    cK
    c1
    caddc
    ppi1i.p
    oveq1i
    3eqtri
end
