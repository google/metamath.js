include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cle.mm"
include "cioc.mm"
include "w3a.mm"
include "simprr.mm"
include "syl6eleq.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "adantr.mm"
include "simpl.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "readdcl.mm"
include "sylancl.mm"
include "elioc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1d.mm"
include "simprl.mm"
include "simp3d.mm"
include "a1i.mm"
include "simp2d.mm"
include "ltadd1dd.mm"
include "lelttrd.mm"
include "ltsubaddd.mm"
include "mpbird.mm"
include "absdifltd.mm"
include "mpbir2and.mm"

theorem efif1olem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let vz: setvar z
  assume efif1olem1.1: |- D = ( A (,] ( A + ( 2 x. _pi ) ) )

  disjoint A y
  disjoint D y
  disjoint y z
  assert |- ( ( A e. RR /\ ( x e. D /\ y e. D ) ) -> ( abs ` ( x - y ) ) < ( 2 x. _pi ) )

  proof
    cA
    cr
    wcel
    #
    vx
    cv
    #
    cD
    wcel
    #
    vy
    cv
    #
    cD
    wcel
    #
    wa
    #
    wa
    #
    @1
    @3
    cmin
    co
    cabs
    cfv
    c2
    cpi
    cmul
    co
    #
    clt
    wbr
    @3
    @7
    cmin
    co
    @1
    clt
    wbr
    #
    @1
    @3
    @7
    caddc
    co
    #
    clt
    wbr
    @6
    @8
    @3
    @1
    @7
    caddc
    co
    #
    clt
    wbr
    @6
    @3
    cA
    @7
    caddc
    co
    #
    @10
    @6
    @3
    cr
    wcel
    #
    cA
    @3
    clt
    wbr
    #
    @3
    @11
    cle
    wbr
    #
    @6
    @3
    cA
    @11
    cioc
    co
    #
    wcel
    #
    @12
    @13
    @14
    w3a
    #
    @6
    @3
    cD
    @15
    @0
    @2
    @4
    simprr
    efif1olem1.1
    syl6eleq
    @6
    cA
    cxr
    wcel
    #
    @11
    cr
    wcel
    #
    @16
    @17
    wb
    @0
    @18
    @5
    cA
    rexr
    adantr
    #
    @6
    @0
    @7
    cr
    wcel
    #
    @19
    @0
    @5
    simpl
    #
    c2
    cpi
    2re
    pire
    remulcli
    #
    cA
    @7
    readdcl
    sylancl
    #
    cA
    @11
    @3
    elioc2
    syl2anc
    mpbid
    #
    simp1d
    #
    @24
    @6
    @1
    cr
    wcel
    #
    @21
    @10
    cr
    wcel
    @6
    @27
    cA
    @1
    clt
    wbr
    #
    @1
    @11
    cle
    wbr
    #
    @6
    @1
    @15
    wcel
    #
    @27
    @28
    @29
    w3a
    #
    @6
    @1
    cD
    @15
    @0
    @2
    @4
    simprl
    efif1olem1.1
    syl6eleq
    @6
    @18
    @19
    @30
    @31
    wb
    @20
    @24
    cA
    @11
    @1
    elioc2
    syl2anc
    mpbid
    #
    simp1d
    #
    @23
    @1
    @7
    readdcl
    sylancl
    @6
    @12
    @13
    @14
    @25
    simp3d
    @6
    cA
    @1
    @7
    @22
    @33
    @21
    @6
    @23
    a1i
    #
    @6
    @27
    @28
    @29
    @32
    simp2d
    ltadd1dd
    lelttrd
    @6
    @3
    @7
    @1
    @26
    @34
    @33
    ltsubaddd
    mpbird
    @6
    @1
    @11
    @9
    @33
    @24
    @6
    @12
    @21
    @9
    cr
    wcel
    @26
    @23
    @3
    @7
    readdcl
    sylancl
    @6
    @27
    @28
    @29
    @32
    simp3d
    @6
    cA
    @3
    @7
    @22
    @26
    @34
    @6
    @12
    @13
    @14
    @25
    simp2d
    ltadd1dd
    lelttrd
    @6
    @1
    @3
    @7
    @33
    @26
    @34
    absdifltd
    mpbir2and
end
