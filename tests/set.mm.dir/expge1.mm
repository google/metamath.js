include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cv.mm"
include "crab.mm"
include "wa.mm"
include "breq2.mm"
include "elrab.mm"
include "cc.mm"
include "ssrab2.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cmul.mm"
include "remulcl.mm"
include "ad2ant2r.mm"
include "1t1e1.mm"
include "cc0.mm"
include "wi.mm"
include "1re.mm"
include "0le1.mm"
include "pm3.2i.mm"
include "jctl.mm"
include "lemul12a.mm"
include "syl2an.mm"
include "imp.mm"
include "syl5eqbrr.mm"
include "an4s.mm"
include "sylanbrc.mm"
include "syl2anb.mm"
include "1le1.mm"
include "mpbir2an.mm"
include "expcllem.mm"
include "sylanbr.mm"
include "3impa.mm"
include "3com23.mm"
include "simprbi.mm"
include "syl.mm"

theorem expge1
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ N e. NN0 /\ 1 <_ A ) -> 1 <_ ( A ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    w3a
    cA
    cN
    cexp
    co
    #
    c1
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
    c1
    @3
    cle
    wbr
    #
    @0
    @2
    @1
    @7
    @0
    @2
    @1
    @7
    @0
    @2
    wa
    cA
    @6
    wcel
    @1
    @7
    @5
    @2
    vz
    cA
    cr
    @4
    cA
    c1
    cle
    breq2
    elrab
    vx
    vy
    cA
    cN
    @6
    @6
    cr
    cc
    @5
    vz
    cr
    ssrab2
    ax-resscn
    sstri
    vx
    cv
    #
    @6
    wcel
    @9
    cr
    wcel
    #
    c1
    @9
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
    c1
    @13
    cle
    wbr
    #
    wa
    #
    @9
    @13
    cmul
    co
    #
    @6
    wcel
    #
    @13
    @6
    wcel
    @5
    @11
    vz
    @9
    cr
    @4
    @9
    c1
    cle
    breq2
    elrab
    @5
    @15
    vz
    @13
    cr
    @4
    @13
    c1
    cle
    breq2
    elrab
    @12
    @16
    wa
    @17
    cr
    wcel
    #
    c1
    @17
    cle
    wbr
    #
    @18
    @10
    @14
    @19
    @11
    @15
    @9
    @13
    remulcl
    ad2ant2r
    @10
    @14
    @11
    @15
    @20
    @10
    @14
    wa
    #
    @11
    @15
    wa
    #
    wa
    c1
    c1
    c1
    cmul
    co
    #
    @17
    cle
    1t1e1
    @21
    @22
    @23
    @17
    cle
    wbr
    #
    @10
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    wa
    #
    @10
    wa
    @27
    @14
    wa
    @22
    @24
    wi
    @14
    @10
    @27
    @25
    @26
    1re
    0le1
    pm3.2i
    #
    jctl
    @14
    @27
    @28
    jctl
    c1
    @9
    c1
    @13
    lemul12a
    syl2an
    imp
    syl5eqbrr
    an4s
    @5
    @20
    vz
    @17
    cr
    @4
    @17
    c1
    cle
    breq2
    elrab
    sylanbrc
    syl2anb
    c1
    @6
    wcel
    @25
    c1
    c1
    cle
    wbr
    #
    1re
    1le1
    @5
    @29
    vz
    c1
    cr
    @4
    c1
    c1
    cle
    breq2
    elrab
    mpbir2an
    expcllem
    sylanbr
    3impa
    3com23
    @7
    @3
    cr
    wcel
    @8
    @5
    @8
    vz
    @3
    cr
    @4
    @3
    c1
    cle
    breq2
    elrab
    simprbi
    syl
end
