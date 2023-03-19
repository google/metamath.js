include "cplusg.mm"
include "cfv.mm"
include "cabv.mm"
include "wceq.mm"
include "a1i.mm"
include "cbs.mm"
include "eqidd.mm"
include "cmulr.mm"
include "c0g.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "cif.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "0re.mm"
include "1re.mm"
include "keepel.mm"
include "fmptd.mm"
include "crg.mm"
include "ring0cl.mm"
include "iftrue.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "0lt1.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "1ex.mm"
include "ifex.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"
include "3adant1.mm"
include "syl5breqr.mm"
include "cmul.mm"
include "co.mm"
include "1t1e1.mm"
include "eqcomi.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "syl.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "simp2r.mm"
include "simp3r.mm"
include "oveq12d.mm"
include "3eqtr4a.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "breq1.mm"
include "0le2.mm"
include "1le2.mm"
include "keephyp.mm"
include "df-2.mm"
include "breqtri.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "eqid.mm"
include "grpcl.mm"
include "3brtr4d.mm"
include "isabvd.mm"

theorem abvtrivd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let c.0: class .0.
  assume abvtriv.a: |- A = ( AbsVal ` R )
  assume abvtriv.b: |- B = ( Base ` R )
  assume abvtriv.z: |- .0. = ( 0g ` R )
  assume abvtriv.f: |- F = ( x e. B |-> if ( x = .0. , 0 , 1 ) )
  assume abvtrivd.1: |- .x. = ( .r ` R )
  assume abvtrivd.2: |- ( ph -> R e. Ring )
  assume abvtrivd.3: |- ( ( ph /\ ( y e. B /\ y =/= .0. ) /\ ( z e. B /\ z =/= .0. ) ) -> ( y .x. z ) =/= .0. )

  disjoint .0. x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint .x. x
  disjoint B x
  assert |- ( ph -> F e. A )

  proof
    wph
    vy
    vz
    cA
    cB
    cR
    cplusg
    cfv
    #
    cR
    c.x
    cF
    c.0
    cA
    cR
    cabv
    cfv
    wceq
    wph
    abvtriv.a
    a1i
    cB
    cR
    cbs
    cfv
    wceq
    wph
    abvtriv.b
    a1i
    wph
    @0
    eqidd
    c.x
    cR
    cmulr
    cfv
    wceq
    wph
    abvtrivd.1
    a1i
    c.0
    cR
    c0g
    cfv
    wceq
    wph
    abvtriv.z
    a1i
    abvtrivd.2
    wph
    vx
    cB
    vx
    cv
    #
    c.0
    wceq
    #
    cc0
    c1
    cif
    #
    cr
    cF
    @3
    cr
    wcel
    wph
    @1
    cB
    wcel
    wa
    @2
    cc0
    c1
    cr
    0re
    1re
    keepel
    a1i
    abvtriv.f
    fmptd
    wph
    cR
    crg
    wcel
    #
    c.0
    cB
    wcel
    c.0
    cF
    cfv
    cc0
    wceq
    abvtrivd.2
    cB
    cR
    c.0
    abvtriv.b
    abvtriv.z
    ring0cl
    vx
    c.0
    @3
    cc0
    cB
    cF
    @2
    cc0
    c1
    iftrue
    abvtriv.f
    c0ex
    fvmpt
    3syl
    wph
    vy
    cv
    #
    cB
    wcel
    #
    @5
    c.0
    wne
    #
    w3a
    cc0
    c1
    @5
    cF
    cfv
    #
    clt
    0lt1
    @6
    @7
    @8
    c1
    wceq
    wph
    @6
    @7
    @8
    @5
    c.0
    wceq
    #
    cc0
    c1
    cif
    #
    c1
    vx
    @5
    @3
    @10
    cB
    cF
    @1
    @5
    wceq
    @2
    @9
    cc0
    c1
    @1
    @5
    c.0
    eqeq1
    ifbid
    abvtriv.f
    @9
    cc0
    c1
    c0ex
    1ex
    ifex
    fvmpt
    #
    @5
    c.0
    cc0
    c1
    ifnefalse
    sylan9eq
    3adant1
    syl5breqr
    wph
    @6
    @7
    wa
    #
    vz
    cv
    #
    cB
    wcel
    #
    @13
    c.0
    wne
    #
    wa
    #
    w3a
    #
    c1
    c1
    c1
    cmul
    co
    #
    @5
    @13
    c.x
    co
    #
    cF
    cfv
    #
    @8
    @13
    cF
    cfv
    #
    cmul
    co
    @18
    c1
    1t1e1
    eqcomi
    @17
    @20
    @19
    c.0
    wceq
    #
    cc0
    c1
    cif
    #
    c1
    @17
    @19
    cB
    wcel
    #
    @20
    @23
    wceq
    @17
    @4
    @6
    @14
    @24
    wph
    @12
    @4
    @16
    abvtrivd.2
    3ad2ant1
    wph
    @6
    @7
    @16
    simp2l
    #
    wph
    @12
    @14
    @15
    simp3l
    #
    cB
    cR
    c.x
    @5
    @13
    abvtriv.b
    abvtrivd.1
    ringcl
    syl3anc
    vx
    @19
    @3
    @23
    cB
    cF
    @1
    @19
    wceq
    @2
    @22
    cc0
    c1
    @1
    @19
    c.0
    eqeq1
    ifbid
    abvtriv.f
    @22
    cc0
    c1
    c0ex
    1ex
    ifex
    fvmpt
    syl
    @17
    @22
    cc0
    c1
    @17
    @19
    c.0
    abvtrivd.3
    neneqd
    iffalsed
    eqtrd
    @17
    @8
    c1
    @21
    c1
    cmul
    @17
    @8
    @10
    c1
    @17
    @6
    @8
    @10
    wceq
    @25
    @11
    syl
    @17
    @9
    cc0
    c1
    @17
    @5
    c.0
    wph
    @6
    @7
    @16
    simp2r
    neneqd
    iffalsed
    eqtrd
    #
    @17
    @21
    @13
    c.0
    wceq
    #
    cc0
    c1
    cif
    #
    c1
    @17
    @14
    @21
    @29
    wceq
    @26
    vx
    @13
    @3
    @29
    cB
    cF
    @1
    @13
    wceq
    @2
    @28
    cc0
    c1
    @1
    @13
    c.0
    eqeq1
    ifbid
    abvtriv.f
    @28
    cc0
    c1
    c0ex
    1ex
    ifex
    fvmpt
    syl
    @17
    @28
    cc0
    c1
    @17
    @13
    c.0
    wph
    @12
    @14
    @15
    simp3r
    neneqd
    iffalsed
    eqtrd
    #
    oveq12d
    3eqtr4a
    @17
    @5
    @13
    @0
    co
    #
    c.0
    wceq
    #
    cc0
    c1
    cif
    #
    c1
    c1
    caddc
    co
    #
    @31
    cF
    cfv
    #
    @8
    @21
    caddc
    co
    cle
    @33
    @34
    cle
    wbr
    @17
    @33
    c2
    @34
    cle
    @32
    cc0
    c2
    cle
    wbr
    c1
    c2
    cle
    wbr
    @33
    c2
    cle
    wbr
    cc0
    c1
    cc0
    @33
    c2
    cle
    breq1
    c1
    @33
    c2
    cle
    breq1
    0le2
    1le2
    keephyp
    df-2
    breqtri
    a1i
    @17
    @31
    cB
    wcel
    #
    @35
    @33
    wceq
    @17
    cR
    cgrp
    wcel
    #
    @6
    @14
    @36
    wph
    @12
    @37
    @16
    wph
    @4
    @37
    abvtrivd.2
    cR
    ringgrp
    syl
    3ad2ant1
    @25
    @26
    cB
    @0
    cR
    @5
    @13
    abvtriv.b
    @0
    eqid
    grpcl
    syl3anc
    vx
    @31
    @3
    @33
    cB
    cF
    @1
    @31
    wceq
    @2
    @32
    cc0
    c1
    @1
    @31
    c.0
    eqeq1
    ifbid
    abvtriv.f
    @32
    cc0
    c1
    c0ex
    1ex
    ifex
    fvmpt
    syl
    @17
    @8
    c1
    @21
    c1
    caddc
    @27
    @30
    oveq12d
    3brtr4d
    isabvd
end
