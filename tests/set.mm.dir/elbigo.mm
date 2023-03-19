include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cbigo.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cdm.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "crab.mm"
include "bigoval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "dmeq.mm"
include "ineq1d.mm"
include "fveq1.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "elbigofrcl.mm"
include "pm4.71ri.mm"
include "3anan12.mm"
include "3bitr4i.mm"

theorem elbigo
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vf: setvar f
  let vk: setvar k

  disjoint G x
  disjoint G m
  disjoint G y
  disjoint m x
  disjoint x y
  disjoint m y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G f
  disjoint f g
  disjoint g x
  disjoint g m
  disjoint g y
  disjoint f x
  disjoint f m
  disjoint f y
  disjoint F f
  disjoint k x
  assert |- ( F e. ( _O ` G ) <-> ( F e. ( RR ^pm RR ) /\ G e. ( RR ^pm RR ) /\ E. x e. RR E. m e. RR A. y e. ( dom F i^i ( x [,) +oo ) ) ( F ` y ) <_ ( m x. ( G ` y ) ) ) )

  proof
    cG
    cr
    cr
    cpm
    co
    #
    wcel
    #
    cF
    cG
    cbigo
    cfv
    #
    wcel
    #
    wa
    @1
    cF
    @0
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    #
    vm
    cv
    @5
    cG
    cfv
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cF
    cdm
    #
    vx
    cv
    cpnf
    cico
    co
    #
    cin
    #
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    wa
    #
    wa
    @3
    @4
    @1
    @13
    w3a
    @1
    @3
    @14
    @1
    @3
    cF
    @5
    vf
    cv
    #
    cfv
    #
    @7
    cle
    wbr
    #
    vy
    @15
    cdm
    #
    @10
    cin
    #
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    vf
    @0
    crab
    #
    wcel
    @14
    @1
    @2
    @22
    cF
    vx
    vy
    vf
    vm
    cG
    bigoval
    eleq2d
    @21
    @13
    vf
    cF
    @0
    @15
    cF
    wceq
    #
    @20
    @12
    vx
    vm
    cr
    cr
    @23
    @17
    @8
    vy
    @19
    @11
    @23
    @18
    @9
    @10
    @15
    cF
    dmeq
    ineq1d
    @23
    @16
    @6
    @7
    cle
    @5
    @15
    cF
    fveq1
    breq1d
    raleqbidv
    2rexbidv
    elrab
    syl6bb
    pm5.32i
    @3
    @1
    cF
    cG
    elbigofrcl
    pm4.71ri
    @4
    @1
    @13
    3anan12
    3bitr4i
end
