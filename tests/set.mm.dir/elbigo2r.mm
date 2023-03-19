include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cbigo.mm"
include "wrex.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "oveq1.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "rspc2ev.mm"
include "3ad2ant3.mm"
include "wb.mm"
include "elbigo2.mm"
include "3adant3.mm"
include "mpbird.mm"

theorem elbigo2r
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cM: class M
  let vg: setvar g
  let vf: setvar f
  let vm: setvar m
  let vy: setvar y
  let vk: setvar k

  disjoint G x
  disjoint F x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint M x
  disjoint G g
  disjoint G f
  disjoint G m
  disjoint G y
  disjoint f g
  disjoint g x
  disjoint g m
  disjoint g y
  disjoint f x
  disjoint f m
  disjoint f y
  disjoint m x
  disjoint x y
  disjoint m y
  disjoint F f
  disjoint F m
  disjoint F y
  disjoint A m
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint C m
  disjoint C y
  disjoint M m
  disjoint k x
  assert |- ( ( ( G : A --> RR /\ A C_ RR ) /\ ( F : B --> RR /\ B C_ A ) /\ ( C e. RR /\ M e. RR /\ A. x e. B ( C <_ x -> ( F ` x ) <_ ( M x. ( G ` x ) ) ) ) ) -> F e. ( _O ` G ) )

  proof
    cA
    cr
    cG
    wf
    cA
    cr
    wss
    wa
    #
    cB
    cr
    cF
    wf
    cB
    cA
    wss
    wa
    #
    cC
    cr
    wcel
    cM
    cr
    wcel
    cC
    vx
    cv
    #
    cle
    wbr
    #
    @2
    cF
    cfv
    #
    cM
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
    wi
    #
    vx
    cB
    wral
    #
    w3a
    #
    w3a
    cF
    cG
    cbigo
    cfv
    wcel
    #
    vy
    cv
    #
    @2
    cle
    wbr
    #
    @4
    vm
    cv
    #
    @5
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    vx
    cB
    wral
    #
    vm
    cr
    wrex
    vy
    cr
    wrex
    #
    @10
    @0
    @19
    @1
    @18
    @9
    @3
    @16
    wi
    #
    vx
    cB
    wral
    vy
    vm
    cC
    cM
    cr
    cr
    @12
    cC
    wceq
    #
    @17
    @20
    vx
    cB
    @21
    @13
    @3
    @16
    @12
    cC
    @2
    cle
    breq1
    imbi1d
    ralbidv
    @14
    cM
    wceq
    #
    @20
    @8
    vx
    cB
    @22
    @16
    @7
    @3
    @22
    @15
    @6
    @4
    cle
    @14
    cM
    @5
    cmul
    oveq1
    breq2d
    imbi2d
    ralbidv
    rspc2ev
    3ad2ant3
    @0
    @1
    @11
    @19
    wb
    @10
    vy
    vx
    cA
    cB
    vm
    cF
    cG
    elbigo2
    3adant3
    mpbird
end
