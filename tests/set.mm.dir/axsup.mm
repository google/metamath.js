include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "cltrr.mm"
include "ax-pre-sup.mm"
include "3expia.mm"
include "wb.mm"
include "wcel.mm"
include "ssel2.mm"
include "ltxrlt.mm"
include "sylan.mm"
include "an32s.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "adantr.mm"
include "ancoms.mm"
include "notbid.mm"
include "adantll.mm"
include "adantlr.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "3imtr4d.mm"
include "3impia.mm"

theorem axsup
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y < x ) -> E. x e. RR ( A. y e. A -. x < y /\ A. y e. RR ( y < x -> E. z e. A y < z ) ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    @3
    @2
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @4
    @2
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    wrex
    #
    @0
    @1
    wa
    @2
    @3
    cltrr
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    @3
    @2
    cltrr
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @17
    @2
    @10
    cltrr
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    wrex
    #
    @6
    @16
    @0
    @1
    @19
    @28
    vx
    vy
    vz
    cA
    ax-pre-sup
    3expia
    @0
    @6
    @19
    wb
    @1
    @0
    @5
    @18
    vx
    cr
    @0
    @3
    cr
    wcel
    #
    wa
    #
    @4
    @17
    vy
    cA
    @0
    @2
    cA
    wcel
    #
    @29
    @4
    @17
    wb
    #
    @0
    @31
    wa
    #
    @2
    cr
    wcel
    #
    @29
    @32
    cA
    cr
    @2
    ssel2
    #
    @2
    @3
    ltxrlt
    #
    sylan
    an32s
    ralbidva
    rexbidva
    adantr
    @0
    @16
    @28
    wb
    @1
    @0
    @15
    @27
    vx
    cr
    @30
    @9
    @22
    @14
    @26
    @30
    @8
    @21
    vy
    cA
    @30
    @31
    wa
    @7
    @20
    @0
    @31
    @29
    @7
    @20
    wb
    #
    @33
    @34
    @29
    @37
    @35
    @29
    @34
    @37
    @3
    @2
    ltxrlt
    ancoms
    sylan
    an32s
    notbid
    ralbidva
    @30
    @13
    @25
    vy
    cr
    @30
    @34
    wa
    @4
    @17
    @12
    @24
    @29
    @34
    @32
    @0
    @34
    @29
    @32
    @36
    ancoms
    adantll
    @0
    @34
    @12
    @24
    wb
    @29
    @0
    @34
    wa
    @11
    @23
    vz
    cA
    @0
    @10
    cA
    wcel
    #
    @34
    @11
    @23
    wb
    #
    @0
    @38
    wa
    @10
    cr
    wcel
    #
    @34
    @39
    cA
    cr
    @10
    ssel2
    @34
    @40
    @39
    @2
    @10
    ltxrlt
    ancoms
    sylan
    an32s
    rexbidva
    adantlr
    imbi12d
    ralbidva
    anbi12d
    rexbidva
    adantr
    3imtr4d
    3impia
end
