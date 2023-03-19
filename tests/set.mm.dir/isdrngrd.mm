include "coppr.mm"
include "cfv.mm"
include "cdr.mm"
include "wcel.mm"
include "cmulr.mm"
include "cbs.mm"
include "eqid.mm"
include "opprbas.mm"
include "syl6eq.mm"
include "eqidd.mm"
include "c0g.mm"
include "oppr0.mm"
include "cur.mm"
include "oppr1.mm"
include "crg.mm"
include "opprring.mm"
include "syl.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "3anbi2d.mm"
include "oveq1.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "opprmul.mm"
include "syl6eqr.mm"
include "eqnetrrd.mm"
include "3com23.mm"
include "chvarv.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "isdrngd.mm"
include "opprdrng.mm"
include "sylibr.mm"

theorem isdrngrd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cI: class I
  let c.0: class .0.
  let vz: setvar z
  assume isdrngd.b: |- ( ph -> B = ( Base ` R ) )
  assume isdrngd.t: |- ( ph -> .x. = ( .r ` R ) )
  assume isdrngd.z: |- ( ph -> .0. = ( 0g ` R ) )
  assume isdrngd.u: |- ( ph -> .1. = ( 1r ` R ) )
  assume isdrngd.r: |- ( ph -> R e. Ring )
  assume isdrngd.n: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) /\ ( y e. B /\ y =/= .0. ) ) -> ( x .x. y ) =/= .0. )
  assume isdrngd.o: |- ( ph -> .1. =/= .0. )
  assume isdrngd.i: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) ) -> I e. B )
  assume isdrngd.j: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) ) -> I =/= .0. )
  assume isdrngrd.k: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) ) -> ( x .x. I ) = .1. )

  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint .1. x
  disjoint .1. y
  disjoint B x
  disjoint B y
  disjoint I y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint .x. x
  disjoint .x. y
  disjoint x z
  disjoint y z
  disjoint .0. z
  disjoint .1. z
  disjoint B z
  disjoint I z
  disjoint R z
  disjoint ph z
  disjoint .x. z
  assert |- ( ph -> R e. DivRing )

  proof
    wph
    cR
    coppr
    cfv
    #
    cdr
    wcel
    cR
    cdr
    wcel
    wph
    vx
    vz
    cB
    @0
    @0
    cmulr
    cfv
    #
    c.1
    cI
    c.0
    wph
    cB
    cR
    cbs
    cfv
    #
    @0
    cbs
    cfv
    isdrngd.b
    @2
    cR
    @0
    @0
    eqid
    #
    @2
    eqid
    #
    opprbas
    syl6eq
    wph
    @1
    eqidd
    wph
    c.0
    cR
    c0g
    cfv
    #
    @0
    c0g
    cfv
    isdrngd.z
    cR
    @0
    @5
    @3
    @5
    eqid
    oppr0
    syl6eq
    wph
    c.1
    cR
    cur
    cfv
    #
    @0
    cur
    cfv
    isdrngd.u
    cR
    @6
    @0
    @3
    @6
    eqid
    oppr1
    syl6eq
    wph
    cR
    crg
    wcel
    @0
    crg
    wcel
    isdrngd.r
    cR
    @0
    @3
    opprring
    syl
    wph
    vy
    cv
    #
    cB
    wcel
    #
    @7
    c.0
    wne
    #
    wa
    #
    vz
    cv
    #
    cB
    wcel
    #
    @11
    c.0
    wne
    #
    wa
    #
    w3a
    #
    @7
    @11
    @1
    co
    #
    c.0
    wne
    #
    wi
    #
    wph
    vx
    cv
    #
    cB
    wcel
    #
    @19
    c.0
    wne
    #
    wa
    #
    @14
    w3a
    #
    @19
    @11
    @1
    co
    #
    c.0
    wne
    #
    wi
    vy
    vx
    @7
    @19
    wceq
    #
    @15
    @23
    @17
    @25
    @26
    @10
    @22
    wph
    @14
    @26
    @8
    @20
    @9
    @21
    @7
    @19
    cB
    eleq1
    @7
    @19
    c.0
    neeq1
    anbi12d
    3anbi2d
    @26
    @16
    @24
    c.0
    @7
    @19
    @11
    @1
    oveq1
    neeq1d
    imbi12d
    wph
    @10
    @22
    w3a
    #
    @7
    @19
    @1
    co
    #
    c.0
    wne
    #
    wi
    @18
    vx
    vz
    @19
    @11
    wceq
    #
    @27
    @15
    @29
    @17
    @30
    @22
    @14
    wph
    @10
    @30
    @20
    @12
    @21
    @13
    @19
    @11
    cB
    eleq1
    @19
    @11
    c.0
    neeq1
    anbi12d
    3anbi3d
    @30
    @28
    @16
    c.0
    @19
    @11
    @7
    @1
    oveq2
    neeq1d
    imbi12d
    wph
    @22
    @10
    @29
    wph
    @22
    @10
    w3a
    #
    @19
    @7
    c.x
    co
    #
    @28
    c.0
    @31
    @32
    @19
    @7
    cR
    cmulr
    cfv
    #
    co
    @28
    @31
    c.x
    @33
    @19
    @7
    wph
    @22
    c.x
    @33
    wceq
    #
    @10
    isdrngd.t
    3ad2ant1
    oveqd
    @2
    cR
    @1
    @33
    @0
    @7
    @19
    @4
    @33
    eqid
    #
    @3
    @1
    eqid
    #
    opprmul
    syl6eqr
    isdrngd.n
    eqnetrrd
    3com23
    chvarv
    chvarv
    isdrngd.o
    isdrngd.i
    isdrngd.j
    wph
    @22
    wa
    #
    cI
    @19
    @1
    co
    @19
    cI
    @33
    co
    #
    c.1
    @2
    cR
    @1
    @33
    @0
    cI
    @19
    @4
    @35
    @3
    @36
    opprmul
    @37
    @19
    cI
    c.x
    co
    @38
    c.1
    @37
    c.x
    @33
    @19
    cI
    wph
    @34
    @22
    isdrngd.t
    adantr
    oveqd
    isdrngrd.k
    eqtr3d
    syl5eq
    isdrngd
    cR
    @0
    @3
    opprdrng
    sylibr
end
