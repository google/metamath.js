include "wcel.mm"
include "cestrc.mm"
include "cfv.mm"
include "crngh.mm"
include "crng.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "co.mm"
include "ccat.mm"
include "id.mm"
include "eqidd.mm"
include "rngcval.mm"
include "eqid.mm"
include "wceq.mm"
include "incom.mm"
include "a1i.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "rnghmsubcsetc.mm"
include "subccat.mm"
include "eqeltrd.mm"

theorem rngccat
  let cC: class C
  let cU: class U
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume rngccat.c: |- C = ( RngCat ` U )


  assert |- ( U e. V -> C e. Cat )

  proof
    cU
    cV
    wcel
    #
    cC
    cU
    cestrc
    cfv
    #
    crngh
    cU
    crng
    cin
    #
    @2
    cxp
    #
    cres
    #
    cresc
    co
    #
    ccat
    @0
    @2
    cC
    cU
    @4
    cV
    rngccat.c
    @0
    id
    #
    @0
    @2
    eqidd
    @0
    @4
    eqidd
    rngcval
    @0
    @1
    @5
    @4
    @5
    eqid
    @0
    crng
    cU
    cin
    #
    @1
    cU
    @4
    cV
    @1
    eqid
    @6
    @0
    @7
    eqidd
    @0
    @3
    @7
    @7
    cxp
    crngh
    @0
    @2
    @7
    @2
    @7
    wceq
    @0
    cU
    crng
    incom
    a1i
    sqxpeqd
    reseq2d
    rnghmsubcsetc
    subccat
    eqeltrd
end
