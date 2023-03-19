include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "crp.mm"
include "wceq.mm"
include "1zzd.mm"
include "znegcld.mm"
include "modmul1.mm"
include "syl221anc.mm"
include "recnd.mm"
include "1cnd.mm"
include "negcld.mm"
include "mulcomd.mm"
include "mulm1d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"

theorem modnegd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume modnegd.1: |- ( ph -> A e. RR )
  assume modnegd.2: |- ( ph -> B e. RR )
  assume modnegd.3: |- ( ph -> C e. RR+ )
  assume modnegd.4: |- ( ph -> ( A mod C ) = ( B mod C ) )


  assert |- ( ph -> ( -u A mod C ) = ( -u B mod C ) )

  proof
    wph
    cA
    c1
    cneg
    #
    cmul
    co
    #
    cC
    cmo
    co
    #
    cB
    @0
    cmul
    co
    #
    cC
    cmo
    co
    #
    cA
    cneg
    #
    cC
    cmo
    co
    cB
    cneg
    #
    cC
    cmo
    co
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    cz
    wcel
    cC
    crp
    wcel
    cA
    cC
    cmo
    co
    cB
    cC
    cmo
    co
    wceq
    @2
    @4
    wceq
    modnegd.1
    modnegd.2
    wph
    c1
    wph
    1zzd
    znegcld
    modnegd.3
    modnegd.4
    cA
    cB
    @0
    cC
    modmul1
    syl221anc
    wph
    @1
    @5
    cC
    cmo
    wph
    @1
    @0
    cA
    cmul
    co
    @5
    wph
    cA
    @0
    wph
    cA
    modnegd.1
    recnd
    #
    wph
    c1
    wph
    1cnd
    negcld
    #
    mulcomd
    wph
    cA
    @7
    mulm1d
    eqtrd
    oveq1d
    wph
    @3
    @6
    cC
    cmo
    wph
    @3
    @0
    cB
    cmul
    co
    @6
    wph
    cB
    @0
    wph
    cB
    modnegd.2
    recnd
    #
    @8
    mulcomd
    wph
    cB
    @9
    mulm1d
    eqtrd
    oveq1d
    3eqtr3d
end
