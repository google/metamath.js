include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cid.mm"
include "cdm.mm"
include "cuni.mm"
include "cif.mm"
include "pmtrdifellem2.mm"
include "adantr.mm"
include "eleq2d.mm"
include "difeq1d.mm"
include "unieqd.mm"
include "ifbieq1d.mm"
include "pmtrdifellem1.mm"
include "eldifi.mm"
include "cpmtr.mm"
include "eqid.mm"
include "pmtrffv.mm"
include "syl2an.mm"
include "3eqtr4rd.mm"
include "ralrimiva.mm"

theorem pmtrdifellem3
  let vx: setvar x
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )
  assume pmtrdifel.0: |- S = ( ( pmTrsp ` N ) ` dom ( Q \ _I ) )

  disjoint Q x
  disjoint T x
  assert |- ( Q e. T -> A. x e. ( N \ { K } ) ( Q ` x ) = ( S ` x ) )

  proof
    cQ
    cT
    wcel
    #
    vx
    cv
    #
    cQ
    cfv
    #
    @1
    cS
    cfv
    #
    wceq
    vx
    cN
    cK
    csn
    #
    cdif
    #
    @0
    @1
    @5
    wcel
    #
    wa
    #
    @1
    cS
    cid
    cdif
    cdm
    #
    wcel
    #
    @8
    @1
    csn
    #
    cdif
    #
    cuni
    #
    @1
    cif
    #
    @1
    cQ
    cid
    cdif
    cdm
    #
    wcel
    #
    @14
    @10
    cdif
    #
    cuni
    #
    @1
    cif
    @3
    @2
    @7
    @9
    @15
    @12
    @17
    @1
    @7
    @8
    @14
    @1
    @0
    @8
    @14
    wceq
    @6
    cQ
    cR
    cS
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    pmtrdifel.0
    pmtrdifellem2
    #
    adantr
    eleq2d
    @0
    @12
    @17
    wceq
    @6
    @0
    @11
    @16
    @0
    @8
    @14
    @10
    @18
    difeq1d
    unieqd
    adantr
    ifbieq1d
    @0
    cS
    cR
    wcel
    @1
    cN
    wcel
    @3
    @13
    wceq
    @6
    cQ
    cR
    cS
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    pmtrdifel.0
    pmtrdifellem1
    @1
    cN
    @4
    eldifi
    cN
    @8
    cR
    cN
    cpmtr
    cfv
    #
    cS
    @1
    @19
    eqid
    pmtrdifel.r
    @8
    eqid
    pmtrffv
    syl2an
    @5
    @14
    cT
    @5
    cpmtr
    cfv
    #
    cQ
    @1
    @20
    eqid
    pmtrdifel.t
    @14
    eqid
    pmtrffv
    3eqtr4rd
    ralrimiva
end
