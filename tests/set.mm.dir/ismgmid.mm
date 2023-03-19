include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crio.mm"
include "wreu.mm"
include "wb.mm"
include "id.mm"
include "wrex.mm"
include "wrmo.mm"
include "mgmidmo.mm"
include "a1i.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "riota2.mm"
include "syl2anr.mm"
include "pm5.32da.mm"
include "riotacl.mm"
include "syl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "pm4.71rd.mm"
include "cio.mm"
include "df-riota.mm"
include "grpidval.mm"
include "eqtr4i.mm"
include "eqeq1i.mm"
include "3bitr2d.mm"

theorem ismgmid
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cU: class U
  let ve: setvar e
  let cG: class G
  let c.0: class .0.
  let cX: class X
  assume ismgmid.b: |- B = ( Base ` G )
  assume ismgmid.o: |- .0. = ( 0g ` G )
  assume ismgmid.p: |- .+ = ( +g ` G )
  assume mgmidcl.e: |- ( ph -> E. e e. B A. x e. B ( ( e .+ x ) = x /\ ( x .+ e ) = x ) )

  disjoint e x
  disjoint .+ e
  disjoint .+ x
  disjoint .0. e
  disjoint .0. x
  disjoint B e
  disjoint B x
  disjoint G e
  disjoint G x
  disjoint U e
  disjoint U x
  disjoint X x
  assert |- ( ph -> ( ( U e. B /\ A. x e. B ( ( U .+ x ) = x /\ ( x .+ U ) = x ) ) <-> .0. = U ) )

  proof
    wph
    cU
    cB
    wcel
    #
    cU
    vx
    cv
    #
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    cU
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    @0
    ve
    cv
    #
    @1
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    @8
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    ve
    cB
    crio
    #
    cU
    wceq
    #
    wa
    @16
    c.0
    cU
    wceq
    #
    wph
    @0
    @7
    @16
    @0
    @0
    @14
    ve
    cB
    wreu
    #
    @7
    @16
    wb
    wph
    @0
    id
    wph
    @14
    ve
    cB
    wrex
    @14
    ve
    cB
    wrmo
    #
    @18
    mgmidcl.e
    @19
    wph
    vx
    ve
    cB
    c.pl
    mgmidmo
    a1i
    @14
    ve
    cB
    reu5
    sylanbrc
    #
    @14
    @7
    ve
    cB
    cU
    @8
    cU
    wceq
    #
    @13
    @6
    vx
    cB
    @21
    @10
    @3
    @12
    @5
    @21
    @9
    @2
    @1
    @8
    cU
    @1
    c.pl
    oveq1
    eqeq1d
    @21
    @11
    @4
    @1
    @8
    cU
    @1
    c.pl
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    riota2
    syl2anr
    pm5.32da
    wph
    @16
    @0
    wph
    @15
    cB
    wcel
    #
    @16
    @0
    wph
    @18
    @22
    @20
    @14
    ve
    cB
    riotacl
    syl
    @15
    cU
    cB
    eleq1
    syl5ibcom
    pm4.71rd
    @16
    @17
    wb
    wph
    @15
    c.0
    cU
    @15
    @8
    cB
    wcel
    @14
    wa
    ve
    cio
    c.0
    @14
    ve
    cB
    df-riota
    vx
    cB
    c.pl
    ve
    cG
    c.0
    ismgmid.b
    ismgmid.p
    ismgmid.o
    grpidval
    eqtr4i
    eqeq1i
    a1i
    3bitr2d
end
