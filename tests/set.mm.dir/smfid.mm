include "cv.mm"
include "cmpt.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "eqid.mm"
include "fmptd.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "a1i.mm"
include "fvmptd.mm"
include "ad2antrr.mm"
include "ad4ant13.mm"
include "breq12d.mm"
include "mpbird.mm"
include "ex.mm"
include "ralrimiva.mm"
include "incsmf.mm"

theorem smfid
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume smfid.j: |- J = ( topGen ` ran (,) )
  assume smfid.b: |- B = ( SalGen ` J )
  assume smfid.a: |- ( ph -> A C_ RR )

  disjoint A x
  disjoint ph x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( x e. A |-> x ) e. ( SMblFn ` B ) )

  proof
    wph
    vy
    vz
    cA
    cB
    vx
    cA
    vx
    cv
    #
    cmpt
    #
    cJ
    smfid.a
    wph
    vx
    cA
    @0
    cr
    @1
    wph
    @0
    cA
    wcel
    #
    wa
    cA
    cr
    @0
    wph
    cA
    cr
    wss
    @2
    smfid.a
    adantr
    wph
    @2
    simpr
    sseldd
    @1
    eqid
    #
    fmptd
    wph
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @4
    @1
    cfv
    #
    @5
    @1
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cA
    wral
    vy
    cA
    wph
    @4
    cA
    wcel
    #
    wa
    #
    @10
    vz
    cA
    @12
    @5
    cA
    wcel
    #
    wa
    #
    @6
    @9
    @14
    @6
    wa
    #
    @9
    @6
    @14
    @6
    simpr
    @15
    @7
    @4
    @8
    @5
    cle
    @12
    @7
    @4
    wceq
    @13
    @6
    @12
    vx
    @4
    @0
    @4
    cA
    @1
    cA
    @1
    @1
    wceq
    #
    @12
    @3
    a1i
    @12
    @0
    @4
    wceq
    simpr
    wph
    @11
    simpr
    #
    @17
    fvmptd
    ad2antrr
    wph
    @13
    @8
    @5
    wceq
    @11
    @6
    wph
    @13
    wa
    #
    vx
    @5
    @0
    @5
    cA
    @1
    cA
    @16
    @18
    @3
    a1i
    @18
    @0
    @5
    wceq
    simpr
    wph
    @13
    simpr
    #
    @19
    fvmptd
    ad4ant13
    breq12d
    mpbird
    ex
    ralrimiva
    ralrimiva
    smfid.j
    smfid.b
    incsmf
end
