include "cui.mm"
include "cfv.mm"
include "cv.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "wa.mm"
include "wcel.mm"
include "rngidpropd.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "dvdsrpropd.mm"
include "breqd.mm"
include "cbs.mm"
include "eqid.mm"
include "opprbas.mm"
include "syl6eq.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "ancom2s.mm"
include "opprmul.mm"
include "3eqtr4g.mm"
include "bitrd.mm"
include "isunit.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem unitpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vz: setvar z
  assume rngidpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume rngidpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume rngidpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint L z
  disjoint ph z
  assert |- ( ph -> ( Unit ` K ) = ( Unit ` L ) )

  proof
    wph
    vz
    cK
    cui
    cfv
    #
    cL
    cui
    cfv
    #
    wph
    vz
    cv
    #
    cK
    cur
    cfv
    #
    cK
    cdsr
    cfv
    #
    wbr
    #
    @2
    @3
    cK
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    wa
    #
    @2
    cL
    cur
    cfv
    #
    cL
    cdsr
    cfv
    #
    wbr
    #
    @2
    @10
    cL
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    wa
    #
    @2
    @0
    wcel
    @2
    @1
    wcel
    wph
    @9
    @2
    @10
    @4
    wbr
    #
    @2
    @10
    @7
    wbr
    #
    wa
    @16
    wph
    @5
    @17
    @8
    @18
    wph
    @3
    @10
    @2
    @4
    wph
    vx
    vy
    cB
    cK
    cL
    rngidpropd.1
    rngidpropd.2
    rngidpropd.3
    rngidpropd
    #
    breq2d
    wph
    @3
    @10
    @2
    @7
    @19
    breq2d
    anbi12d
    wph
    @17
    @12
    @18
    @15
    wph
    @4
    @11
    @2
    @10
    wph
    vx
    vy
    cB
    cK
    cL
    rngidpropd.1
    rngidpropd.2
    rngidpropd.3
    dvdsrpropd
    breqd
    wph
    @7
    @14
    @2
    @10
    wph
    vy
    vx
    cB
    @6
    @13
    wph
    cB
    cK
    cbs
    cfv
    #
    @6
    cbs
    cfv
    rngidpropd.1
    @20
    cK
    @6
    @6
    eqid
    #
    @20
    eqid
    #
    opprbas
    syl6eq
    wph
    cB
    cL
    cbs
    cfv
    #
    @13
    cbs
    cfv
    rngidpropd.2
    @23
    cL
    @13
    @13
    eqid
    #
    @23
    eqid
    #
    opprbas
    syl6eq
    wph
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    wa
    wa
    @28
    @26
    cK
    cmulr
    cfv
    #
    co
    #
    @28
    @26
    cL
    cmulr
    cfv
    #
    co
    #
    @26
    @28
    @6
    cmulr
    cfv
    #
    co
    @26
    @28
    @13
    cmulr
    cfv
    #
    co
    wph
    @29
    @27
    @31
    @33
    wceq
    rngidpropd.3
    ancom2s
    @20
    cK
    @34
    @30
    @6
    @26
    @28
    @22
    @30
    eqid
    @21
    @34
    eqid
    opprmul
    @23
    cL
    @35
    @32
    @13
    @26
    @28
    @25
    @32
    eqid
    @24
    @35
    eqid
    opprmul
    3eqtr4g
    dvdsrpropd
    breqd
    anbi12d
    bitrd
    @4
    cK
    @6
    @0
    @3
    @7
    @2
    @0
    eqid
    @3
    eqid
    @4
    eqid
    @21
    @7
    eqid
    isunit
    @11
    cL
    @13
    @1
    @10
    @14
    @2
    @1
    eqid
    @10
    eqid
    @11
    eqid
    @24
    @14
    eqid
    isunit
    3bitr4g
    eqrdv
end
