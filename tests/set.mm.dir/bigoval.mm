include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cdm.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "cbigo.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-bigo.mm"
include "a1i.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "2rexbidv.mm"
include "rabbidv.mm"
include "adantl.mm"
include "id.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmptd.mm"

theorem bigoval
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vm: setvar m
  let cG: class G
  let vg: setvar g
  let vk: setvar k

  disjoint G f
  disjoint G x
  disjoint G m
  disjoint G y
  disjoint f x
  disjoint f m
  disjoint f y
  disjoint m x
  disjoint x y
  disjoint m y
  disjoint G g
  disjoint f g
  disjoint g x
  disjoint g m
  disjoint g y
  disjoint k x
  assert |- ( G e. ( RR ^pm RR ) -> ( _O ` G ) = { f e. ( RR ^pm RR ) | E. x e. RR E. m e. RR A. y e. ( dom f i^i ( x [,) +oo ) ) ( f ` y ) <_ ( m x. ( G ` y ) ) } )

  proof
    cG
    cr
    cr
    cpm
    co
    #
    wcel
    #
    vg
    cG
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    vm
    cv
    #
    @2
    vg
    cv
    #
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    @3
    cdm
    vx
    cv
    cpnf
    cico
    co
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
    @4
    @5
    @2
    cG
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    @10
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
    @0
    cbigo
    cvv
    cbigo
    vg
    @0
    @13
    cmpt
    wceq
    @1
    vx
    vy
    vf
    vg
    vm
    df-bigo
    a1i
    @6
    cG
    wceq
    #
    @13
    @19
    wceq
    @1
    @20
    @12
    @18
    vf
    @0
    @20
    @11
    @17
    vx
    vm
    cr
    cr
    @20
    @9
    @16
    vy
    @10
    @20
    @8
    @15
    @4
    cle
    @20
    @7
    @14
    @5
    cmul
    @2
    @6
    cG
    fveq1
    oveq2d
    breq2d
    ralbidv
    2rexbidv
    rabbidv
    adantl
    @1
    id
    @19
    cvv
    wcel
    @1
    @18
    vf
    @0
    cr
    cr
    cpm
    ovex
    rabex
    a1i
    fvmptd
end
