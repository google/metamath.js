include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cpsgn.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "cevpm.mm"
include "cdif.mm"
include "simpl.mm"
include "symgtrf.mm"
include "sseli.mm"
include "adantl.mm"
include "eqid.mm"
include "psgnpmtr.mm"
include "psgnodpmr.mm"
include "syl3anc.mm"

theorem pmtrodpm
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  assume evpmodpmf1o.s: |- S = ( SymGrp ` D )
  assume evpmodpmf1o.p: |- P = ( Base ` S )
  assume pmtrodpm.t: |- T = ran ( pmTrsp ` D )


  assert |- ( ( D e. Fin /\ F e. T ) -> F e. ( P \ ( pmEven ` D ) ) )

  proof
    cD
    cfn
    wcel
    #
    cF
    cT
    wcel
    #
    wa
    @0
    cF
    cP
    wcel
    #
    cF
    cD
    cpsgn
    cfv
    #
    cfv
    c1
    cneg
    wceq
    #
    cF
    cP
    cD
    cevpm
    cfv
    cdif
    wcel
    @0
    @1
    simpl
    @1
    @2
    @0
    cT
    cP
    cF
    cP
    cD
    cT
    cS
    pmtrodpm.t
    evpmodpmf1o.s
    evpmodpmf1o.p
    symgtrf
    sseli
    adantl
    @1
    @4
    @0
    cD
    cF
    cT
    cS
    @3
    evpmodpmf1o.s
    pmtrodpm.t
    @3
    eqid
    #
    psgnpmtr
    adantl
    cD
    cP
    cS
    cF
    @3
    evpmodpmf1o.s
    evpmodpmf1o.p
    @5
    psgnodpmr
    syl3anc
end
