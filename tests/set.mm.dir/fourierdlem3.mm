include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "cpi.mm"
include "cneg.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cicc.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem fourierdlem3
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vm: setvar m
  let cM: class M
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem3.1: |- P = ( m e. NN |-> { p e. ( ( -u _pi [,] _pi ) ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = -u _pi /\ ( p ` m ) = _pi ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )

  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint Q i
  disjoint Q p
  disjoint k x
  assert |- ( M e. NN -> ( Q e. ( P ` M ) <-> ( Q e. ( ( -u _pi [,] _pi ) ^m ( 0 ... M ) ) /\ ( ( ( Q ` 0 ) = -u _pi /\ ( Q ` M ) = _pi ) /\ A. i e. ( 0 ..^ M ) ( Q ` i ) < ( Q ` ( i + 1 ) ) ) ) ) )

  proof
    cM
    cn
    wcel
    #
    cQ
    cM
    cP
    cfv
    #
    wcel
    cQ
    cc0
    vp
    cv
    #
    cfv
    #
    cpi
    cneg
    #
    wceq
    #
    cM
    @2
    cfv
    #
    cpi
    wceq
    #
    wa
    #
    vi
    cv
    #
    @2
    cfv
    #
    @9
    c1
    caddc
    co
    #
    @2
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    @4
    cpi
    cicc
    co
    #
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    wcel
    cQ
    @19
    wcel
    cc0
    cQ
    cfv
    #
    @4
    wceq
    #
    cM
    cQ
    cfv
    #
    cpi
    wceq
    #
    wa
    #
    @9
    cQ
    cfv
    #
    @11
    cQ
    cfv
    #
    clt
    wbr
    #
    vi
    @14
    wral
    #
    wa
    #
    wa
    @0
    @1
    @20
    cQ
    vm
    cM
    @5
    vm
    cv
    #
    @2
    cfv
    #
    cpi
    wceq
    #
    wa
    #
    @13
    vi
    cc0
    @31
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    @17
    cc0
    @31
    cfz
    co
    #
    cmap
    co
    #
    crab
    @20
    cn
    cP
    @31
    cM
    wceq
    #
    @37
    @16
    vp
    @39
    @19
    @40
    @38
    @18
    @17
    cmap
    @31
    cM
    cc0
    cfz
    oveq2
    oveq2d
    @40
    @34
    @8
    @36
    @15
    @40
    @33
    @7
    @5
    @40
    @32
    @6
    cpi
    @31
    cM
    @2
    fveq2
    eqeq1d
    anbi2d
    @40
    @13
    vi
    @35
    @14
    @31
    cM
    cc0
    cfzo
    oveq2
    raleqdv
    anbi12d
    rabeqbidv
    fourierdlem3.1
    @16
    vp
    @19
    @17
    @18
    cmap
    ovex
    rabex
    fvmpt
    eleq2d
    @16
    @30
    vp
    cQ
    @19
    @2
    cQ
    wceq
    #
    @8
    @25
    @15
    @29
    @41
    @5
    @22
    @7
    @24
    @41
    @3
    @21
    @4
    cc0
    @2
    cQ
    fveq1
    eqeq1d
    @41
    @6
    @23
    cpi
    cM
    @2
    cQ
    fveq1
    eqeq1d
    anbi12d
    @41
    @13
    @28
    vi
    @14
    @41
    @10
    @26
    @12
    @27
    clt
    @9
    @2
    cQ
    fveq1
    @11
    @2
    cQ
    fveq1
    breq12d
    ralbidv
    anbi12d
    elrab
    syl6bb
end
