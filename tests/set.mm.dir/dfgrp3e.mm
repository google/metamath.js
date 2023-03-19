include "cgrp.mm"
include "wcel.mm"
include "csgrp.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "dfgrp3.mm"
include "simp2.mm"
include "wi.mm"
include "cmgm.mm"
include "sgrpmgm.mm"
include "adantr.mm"
include "simpr.mm"
include "mgmcl.mm"
include "syl3anc.mm"
include "sgrpass.mm"
include "3anassrs.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "ex.mm"
include "ralimdva.mm"
include "a1d.mm"
include "3imp.mm"
include "jca.mm"
include "wex.mm"
include "n0.mm"
include "3simpa.mm"
include "2ralimi.mm"
include "issgrpn0.mm"
include "syl5ibr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "imp.mm"
include "simpl.mm"
include "simp3.mm"
include "adantl.mm"
include "impbii.mm"
include "bitri.mm"

theorem dfgrp3e
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let vr: setvar r
  let vl: setvar l
  let va: setvar a
  let vi: setvar i
  let vu: setvar u
  let vw: setvar w
  assume dfgrp3.b: |- B = ( Base ` G )
  assume dfgrp3.p: |- .+ = ( +g ` G )

  disjoint B l
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint l r
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G l
  disjoint G r
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint .+ l
  disjoint .+ r
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint B a
  disjoint B i
  disjoint B u
  disjoint B w
  disjoint a i
  disjoint a l
  disjoint a r
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint i l
  disjoint i r
  disjoint i u
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint l u
  disjoint l w
  disjoint r u
  disjoint r w
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G a
  disjoint G i
  disjoint G u
  disjoint G w
  disjoint .+ a
  disjoint .+ i
  disjoint .+ u
  disjoint .+ w
  assert |- ( G e. Grp <-> ( B =/= (/) /\ A. x e. B A. y e. B ( ( x .+ y ) e. B /\ A. z e. B ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) /\ ( E. l e. B ( l .+ x ) = y /\ E. r e. B ( x .+ r ) = y ) ) ) )

  proof
    cG
    cgrp
    wcel
    cG
    csgrp
    wcel
    #
    cB
    c0
    wne
    #
    vl
    cv
    vx
    cv
    #
    c.pl
    co
    vy
    cv
    #
    wceq
    vl
    cB
    wrex
    @2
    vr
    cv
    c.pl
    co
    @3
    wceq
    vr
    cB
    wrex
    wa
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    w3a
    #
    @1
    @2
    @3
    c.pl
    co
    #
    cB
    wcel
    #
    @8
    vz
    cv
    #
    c.pl
    co
    @2
    @3
    @10
    c.pl
    co
    c.pl
    co
    wceq
    #
    vz
    cB
    wral
    #
    @4
    w3a
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    vx
    vy
    cB
    c.pl
    cG
    vr
    vl
    dfgrp3.b
    dfgrp3.p
    dfgrp3
    @7
    @16
    @7
    @1
    @15
    @0
    @1
    @6
    simp2
    @0
    @1
    @6
    @15
    @0
    @6
    @15
    wi
    @1
    @0
    @5
    @14
    vx
    cB
    @0
    @2
    cB
    wcel
    #
    wa
    #
    @4
    @13
    vy
    cB
    @18
    @3
    cB
    wcel
    #
    wa
    #
    @4
    @13
    @20
    @4
    wa
    @9
    @12
    @4
    @20
    @9
    @4
    @20
    cG
    cmgm
    wcel
    #
    @17
    @19
    @9
    @18
    @21
    @19
    @0
    @21
    @17
    cG
    sgrpmgm
    adantr
    adantr
    @18
    @17
    @19
    @0
    @17
    simpr
    adantr
    @18
    @19
    simpr
    cB
    cG
    @2
    @3
    c.pl
    dfgrp3.b
    dfgrp3.p
    mgmcl
    syl3anc
    adantr
    @20
    @12
    @4
    @20
    @11
    vz
    cB
    @0
    @17
    @19
    @10
    cB
    wcel
    @11
    cB
    cG
    @2
    @3
    c.pl
    @10
    dfgrp3.b
    dfgrp3.p
    sgrpass
    3anassrs
    ralrimiva
    adantr
    @20
    @4
    simpr
    3jca
    ex
    ralimdva
    ralimdva
    a1d
    3imp
    jca
    @16
    @0
    @1
    @6
    @1
    @15
    @0
    @1
    va
    cv
    #
    cB
    wcel
    #
    va
    wex
    @15
    @0
    wi
    #
    va
    cB
    n0
    @23
    @24
    va
    @15
    @0
    @23
    @9
    @12
    wa
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @13
    @25
    vx
    vy
    cB
    cB
    @9
    @12
    @4
    3simpa
    2ralimi
    vx
    vy
    vz
    @22
    cB
    cG
    c.pl
    dfgrp3.b
    dfgrp3.p
    issgrpn0
    syl5ibr
    exlimiv
    sylbi
    imp
    @1
    @15
    simpl
    @15
    @6
    @1
    @13
    @4
    vx
    vy
    cB
    cB
    @9
    @12
    @4
    simp3
    2ralimi
    adantl
    3jca
    impbii
    bitri
end
