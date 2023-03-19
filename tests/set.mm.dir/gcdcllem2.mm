include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cpr.mm"
include "wral.mm"
include "weq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "breq2.mm"
include "ralprg.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"

theorem gcdcllem2
  let vz: setvar z
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vx: setvar x
  let cK: class K
  let vy: setvar y
  assume gcdcllem2.1: |- S = { z e. ZZ | A. n e. { M , N } z || n }
  assume gcdcllem2.2: |- R = { z e. ZZ | ( z || M /\ z || N ) }

  disjoint n z
  disjoint M n
  disjoint M z
  disjoint N n
  disjoint N z
  disjoint x z
  disjoint K x
  disjoint K z
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> R = S )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    vx
    cR
    cS
    @0
    vx
    cv
    #
    cS
    wcel
    #
    @1
    cz
    wcel
    #
    @1
    cM
    cdvds
    wbr
    #
    @1
    cN
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    @1
    cR
    wcel
    @2
    @3
    @1
    vn
    cv
    #
    cdvds
    wbr
    #
    vn
    cM
    cN
    cpr
    #
    wral
    #
    wa
    @0
    @7
    vz
    cv
    #
    @8
    cdvds
    wbr
    #
    vn
    @10
    wral
    @11
    vz
    @1
    cz
    cS
    vz
    vx
    weq
    #
    @13
    @9
    vn
    @10
    @12
    @1
    @8
    cdvds
    breq1
    ralbidv
    gcdcllem2.1
    elrab2
    @0
    @11
    @6
    @3
    @9
    @4
    @5
    vn
    cM
    cN
    cz
    cz
    @8
    cM
    @1
    cdvds
    breq2
    @8
    cN
    @1
    cdvds
    breq2
    ralprg
    anbi2d
    syl5bb
    @12
    cM
    cdvds
    wbr
    #
    @12
    cN
    cdvds
    wbr
    #
    wa
    @6
    vz
    @1
    cz
    cR
    @14
    @15
    @4
    @16
    @5
    @12
    @1
    cM
    cdvds
    breq1
    @12
    @1
    cN
    cdvds
    breq1
    anbi12d
    gcdcllem2.2
    elrab2
    syl6rbbr
    eqrdv
end
