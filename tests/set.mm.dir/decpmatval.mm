include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cdecpmat.mm"
include "co.mm"
include "cdm.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "decpmatval0.mm"
include "wceq.mm"
include "cbs.mm"
include "cxp.mm"
include "cmap.mm"
include "wf.mm"
include "eqid.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "fdm.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "3syl.mm"
include "adantr.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "eqtrd.mm"

theorem decpmatval
  let cA: class A
  let cB: class B
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cN: class N
  assume decpmatval.a: |- A = ( N Mat R )
  assume decpmatval.b: |- B = ( Base ` A )

  disjoint B i
  disjoint B j
  disjoint i j
  disjoint K i
  disjoint K j
  disjoint M i
  disjoint M j
  assert |- ( ( M e. B /\ K e. NN0 ) -> ( M decompPMat K ) = ( i e. N , j e. N |-> ( ( coe1 ` ( i M j ) ) ` K ) ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cM
    cK
    cdecpmat
    co
    vi
    vj
    cM
    cdm
    #
    cdm
    #
    @4
    cK
    vi
    cv
    vj
    cv
    cM
    co
    cco1
    cfv
    cfv
    #
    cmpt2
    vi
    vj
    cN
    cN
    @5
    cmpt2
    vi
    vj
    cK
    cM
    cB
    decpmatval0
    @2
    vi
    vj
    @4
    @4
    @5
    cN
    cN
    @5
    @0
    @4
    cN
    wceq
    #
    @1
    @0
    cM
    cR
    cbs
    cfv
    #
    cN
    cN
    cxp
    #
    cmap
    co
    wcel
    @8
    @7
    cM
    wf
    #
    @6
    cA
    cB
    cR
    @7
    cM
    cN
    decpmatval.a
    @7
    eqid
    decpmatval.b
    matbas2i
    cM
    @7
    @8
    elmapi
    @9
    @4
    @8
    cdm
    cN
    @9
    @3
    @8
    @8
    @7
    cM
    fdm
    dmeqd
    cN
    dmxpid
    syl6eq
    3syl
    adantr
    #
    @10
    @2
    @5
    eqidd
    mpt2eq123dv
    eqtrd
end
