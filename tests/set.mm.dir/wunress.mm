include "cvv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cnx.mm"
include "cin.mm"
include "cop.mm"
include "csts.mm"
include "cif.mm"
include "wceq.mm"
include "eqid.mm"
include "ressval.mm"
include "sylan.mm"
include "c1.mm"
include "df-base.mm"
include "wunndx.mm"
include "wunstr.mm"
include "incom.mm"
include "wunin.mm"
include "syl5eqel.mm"
include "wunop.mm"
include "wunsets.mm"
include "ifcld.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "wun0.mm"
include "reldmress.mm"
include "ovprc2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "pm2.61d.mm"

theorem wunress
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cW: class W
  assume wunress.1: |- ( ph -> U e. WUni )
  assume wunress.2: |- ( ph -> _om e. U )
  assume wunress.3: |- ( ph -> W e. U )


  assert |- ( ph -> ( W |`s A ) e. U )

  proof
    wph
    cA
    cvv
    wcel
    #
    cW
    cA
    cress
    co
    #
    cU
    wcel
    #
    wph
    @0
    @2
    wph
    @0
    wa
    @1
    cW
    cbs
    cfv
    #
    cA
    wss
    #
    cW
    cW
    cnx
    cbs
    cfv
    #
    cA
    @3
    cin
    #
    cop
    #
    csts
    co
    #
    cif
    #
    cU
    wph
    cW
    cU
    wcel
    @0
    @1
    @9
    wceq
    wunress.3
    cA
    @3
    @1
    cW
    cU
    cvv
    @1
    eqid
    @3
    eqid
    ressval
    sylan
    wph
    @9
    cU
    wcel
    @0
    wph
    @4
    cW
    @8
    cU
    wunress.3
    wph
    @7
    cW
    cU
    wunress.1
    wunress.3
    wph
    @5
    @6
    cU
    wunress.1
    wph
    cnx
    cU
    cbs
    c1
    df-base
    wunress.1
    wph
    cU
    wunress.1
    wunress.2
    wunndx
    wunstr
    wph
    @6
    @3
    cA
    cin
    cU
    cA
    @3
    incom
    wph
    @3
    cA
    cU
    wunress.1
    wph
    cW
    cU
    cbs
    c1
    df-base
    wunress.1
    wunress.3
    wunstr
    wunin
    syl5eqel
    wunop
    wunsets
    ifcld
    adantr
    eqeltrd
    ex
    wph
    @2
    @0
    wn
    #
    c0
    cU
    wcel
    wph
    cU
    wunress.1
    wun0
    @10
    @1
    c0
    cU
    cW
    cA
    cress
    reldmress
    ovprc2
    eleq1d
    syl5ibrcom
    pm2.61d
end
