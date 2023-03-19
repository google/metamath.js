include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "c2o.mm"
include "cen.mm"
include "cprime.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "breq1d.mm"
include "df-prm.mm"
include "elrab2.mm"

theorem isprm
  let cP: class P
  let vn: setvar n
  let vp: setvar p
  let vz: setvar z

  disjoint P n
  disjoint P p
  disjoint P z
  disjoint n p
  disjoint n z
  disjoint p z
  assert |- ( P e. Prime <-> ( P e. NN /\ { n e. NN | n || P } ~~ 2o ) )

  proof
    vn
    cv
    #
    vp
    cv
    #
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    c2o
    cen
    wbr
    @0
    cP
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    c2o
    cen
    wbr
    vp
    cP
    cn
    cprime
    @1
    cP
    wceq
    #
    @3
    @5
    c2o
    cen
    @6
    @2
    @4
    vn
    cn
    @1
    cP
    @0
    cdvds
    breq2
    rabbidv
    breq1d
    vn
    vp
    df-prm
    elrab2
end
