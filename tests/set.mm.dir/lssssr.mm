include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "clmod.mm"
include "lss0cl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "a1d.mm"
include "wne.mm"
include "sseld.mm"
include "ancrd.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylan2br.mm"
include "exp32.mm"
include "com23.mm"
include "imp4b.mm"
include "syld.mm"
include "pm2.61dane.mm"
include "ssrdv.mm"

theorem lssssr
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lssssr.v: |- V = ( Base ` W )
  assume lssssr.o: |- .0. = ( 0g ` W )
  assume lssssr.s: |- S = ( LSubSp ` W )
  assume lssssr.w: |- ( ph -> W e. LMod )
  assume lssssr.t: |- ( ph -> T C_ V )
  assume lssssr.u: |- ( ph -> U e. S )
  assume lssssr.1: |- ( ( ph /\ x e. ( V \ { .0. } ) ) -> ( x e. T -> x e. U ) )

  disjoint T x
  disjoint U x
  disjoint ph x
  assert |- ( ph -> T C_ U )

  proof
    wph
    vx
    cT
    cU
    wph
    vx
    cv
    #
    cT
    wcel
    #
    @0
    cU
    wcel
    #
    wi
    #
    @0
    c.0
    wph
    @0
    c.0
    wceq
    #
    wa
    #
    @2
    @1
    @5
    @0
    c.0
    cU
    wph
    @4
    simpr
    wph
    c.0
    cU
    wcel
    #
    @4
    wph
    cW
    clmod
    wcel
    cU
    cS
    wcel
    @6
    lssssr.w
    lssssr.u
    cS
    cU
    cW
    c.0
    lssssr.o
    lssssr.s
    lss0cl
    syl2anc
    adantr
    eqeltrd
    a1d
    wph
    @0
    c.0
    wne
    #
    wa
    @1
    @0
    cV
    wcel
    #
    @1
    wa
    #
    @2
    wph
    @1
    @9
    wi
    @7
    wph
    @1
    @8
    wph
    cT
    cV
    @0
    lssssr.t
    sseld
    ancrd
    adantr
    wph
    @7
    @8
    @1
    @2
    wph
    @8
    @7
    @3
    wph
    @8
    @7
    @3
    @8
    @7
    wa
    wph
    @0
    cV
    c.0
    csn
    cdif
    wcel
    @3
    @0
    cV
    c.0
    eldifsn
    lssssr.1
    sylan2br
    exp32
    com23
    imp4b
    syld
    pm2.61dane
    ssrdv
end
