include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "breq2.mm"
include "elrab.mm"
include "cc.mm"
include "ssrab2.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cmul.mm"
include "remulcl.mm"
include "ad2ant2r.mm"
include "mulge0.mm"
include "sylanbrc.mm"
include "syl2anb.mm"
include "c1.mm"
include "1re.mm"
include "0le1.mm"
include "mpbir2an.mm"
include "expcllem.mm"
include "simprbi.mm"
include "syl.mm"
include "sylanbr.mm"
include "3impa.mm"
include "3com23.mm"

theorem expge0
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ N e. NN0 /\ 0 <_ A ) -> 0 <_ ( A ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cN
    cn0
    wcel
    #
    cc0
    cA
    cN
    cexp
    co
    #
    cle
    wbr
    #
    @0
    @1
    @2
    @4
    @0
    @1
    wa
    cA
    cc0
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cr
    crab
    #
    wcel
    #
    @2
    @4
    @6
    @1
    vz
    cA
    cr
    @5
    cA
    cc0
    cle
    breq2
    elrab
    @8
    @2
    wa
    @3
    @7
    wcel
    #
    @4
    vx
    vy
    cA
    cN
    @7
    @7
    cr
    cc
    @6
    vz
    cr
    ssrab2
    ax-resscn
    sstri
    vx
    cv
    #
    @7
    wcel
    @10
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    wa
    #
    vy
    cv
    #
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    wa
    #
    @10
    @14
    cmul
    co
    #
    @7
    wcel
    #
    @14
    @7
    wcel
    @6
    @12
    vz
    @10
    cr
    @5
    @10
    cc0
    cle
    breq2
    elrab
    @6
    @16
    vz
    @14
    cr
    @5
    @14
    cc0
    cle
    breq2
    elrab
    @13
    @17
    wa
    @18
    cr
    wcel
    #
    cc0
    @18
    cle
    wbr
    #
    @19
    @11
    @15
    @20
    @12
    @16
    @10
    @14
    remulcl
    ad2ant2r
    @10
    @14
    mulge0
    @6
    @21
    vz
    @18
    cr
    @5
    @18
    cc0
    cle
    breq2
    elrab
    sylanbrc
    syl2anb
    c1
    @7
    wcel
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    #
    1re
    0le1
    @6
    @22
    vz
    c1
    cr
    @5
    c1
    cc0
    cle
    breq2
    elrab
    mpbir2an
    expcllem
    @9
    @3
    cr
    wcel
    @4
    @6
    @4
    vz
    @3
    cr
    @5
    @3
    cc0
    cle
    breq2
    elrab
    simprbi
    syl
    sylanbr
    3impa
    3com23
end
