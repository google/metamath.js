include "wcel.mm"
include "cestrc.mm"
include "cfv.mm"
include "crh.mm"
include "crg.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "co.mm"
include "ccat.mm"
include "id.mm"
include "eqidd.mm"
include "ringcval.mm"
include "eqid.mm"
include "wceq.mm"
include "incom.mm"
include "a1i.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "rhmsubcsetc.mm"
include "subccat.mm"
include "eqeltrd.mm"

theorem ringccat
  let cC: class C
  let cU: class U
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume ringccat.c: |- C = ( RingCat ` U )


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
    crh
    cU
    crg
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
    ringccat.c
    @0
    id
    #
    @0
    @2
    eqidd
    @0
    @4
    eqidd
    ringcval
    @0
    @1
    @5
    @4
    @5
    eqid
    @0
    crg
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
    crh
    @0
    @2
    @7
    @2
    @7
    wceq
    @0
    cU
    crg
    incom
    a1i
    sqxpeqd
    reseq2d
    rhmsubcsetc
    subccat
    eqeltrd
end
