include "cbigo.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "cdm.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "simp1.mm"
include "wa.mm"
include "wb.mm"
include "cpm.mm"
include "elbigofrcl.mm"
include "reex.mm"
include "elpm2.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "elbigo2.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem elbigoimp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vf: setvar f
  let cB: class B
  let cC: class C
  let cM: class M
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
  disjoint A m
  disjoint A x
  disjoint A y
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
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint M m
  disjoint M x
  disjoint k x
  assert |- ( ( F e. ( _O ` G ) /\ F : A --> RR /\ A C_ dom G ) -> E. x e. RR E. m e. RR A. y e. A ( x <_ y -> ( F ` y ) <_ ( m x. ( G ` y ) ) ) )

  proof
    cF
    cG
    cbigo
    cfv
    wcel
    #
    cA
    cr
    cF
    wf
    #
    cA
    cG
    cdm
    #
    wss
    #
    w3a
    #
    @0
    vx
    cv
    vy
    cv
    #
    cle
    wbr
    @5
    cF
    cfv
    vm
    cv
    @5
    cG
    cfv
    cmul
    co
    cle
    wbr
    wi
    vy
    cA
    wral
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    @0
    @1
    @3
    simp1
    @4
    @2
    cr
    cG
    wf
    @2
    cr
    wss
    wa
    #
    @1
    @3
    wa
    @0
    @6
    wb
    @0
    @1
    @7
    @3
    @0
    cG
    cr
    cr
    cpm
    co
    wcel
    @7
    cF
    cG
    elbigofrcl
    cr
    cr
    cG
    reex
    reex
    elpm2
    sylib
    3ad2ant1
    @0
    @1
    @3
    3simpc
    vx
    vy
    @2
    cA
    vm
    cF
    cG
    elbigo2
    syl2anc
    mpbid
end
