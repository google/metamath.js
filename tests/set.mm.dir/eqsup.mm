include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "crio.mm"
include "wor.mm"
include "adantr.mm"
include "supval2.mm"
include "3simpc.mm"
include "adantl.mm"
include "wreu.mm"
include "wb.mm"
include "simpr1.mm"
include "breq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "supeu.mm"
include "riota2.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "ex.mm"

theorem eqsup
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vw: setvar w
  assume supmo.1: |- ( ph -> R Or A )

  disjoint C y
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R y
  disjoint R z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint C x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R x
  disjoint R w
  disjoint B x
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ph -> ( ( C e. A /\ A. y e. B -. C R y /\ A. y e. A ( y R C -> E. z e. B y R z ) ) -> sup ( B , A , R ) = C ) )

  proof
    wph
    cC
    cA
    wcel
    #
    cC
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @1
    cC
    cR
    wbr
    #
    @1
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    w3a
    #
    cB
    cA
    cR
    csup
    #
    cC
    wceq
    wph
    @9
    wa
    #
    @10
    vx
    cv
    #
    @1
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @1
    @12
    cR
    wbr
    #
    @6
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    crio
    #
    cC
    @11
    vx
    vy
    vz
    cA
    cB
    cR
    wph
    cA
    cR
    wor
    @9
    supmo.1
    adantr
    #
    supval2
    @11
    @4
    @8
    wa
    #
    @20
    cC
    wceq
    #
    @9
    @22
    wph
    @0
    @4
    @8
    3simpc
    adantl
    #
    @11
    @0
    @19
    vx
    cA
    wreu
    @22
    @23
    wb
    wph
    @0
    @4
    @8
    simpr1
    #
    @11
    vx
    vy
    vz
    cA
    cB
    cR
    @21
    @11
    @0
    @22
    @19
    vx
    cA
    wrex
    @25
    @24
    @19
    @22
    vx
    cC
    cA
    @12
    cC
    wceq
    #
    @15
    @4
    @18
    @8
    @26
    @14
    @3
    vy
    cB
    @26
    @13
    @2
    @12
    cC
    @1
    cR
    breq1
    notbid
    ralbidv
    @26
    @17
    @7
    vy
    cA
    @26
    @16
    @5
    @6
    @12
    cC
    @1
    cR
    breq2
    imbi1d
    ralbidv
    anbi12d
    #
    rspcev
    syl2anc
    supeu
    @19
    @22
    vx
    cA
    cC
    @27
    riota2
    syl2anc
    mpbid
    eqtrd
    ex
end
