include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cico.mm"
include "cvol.mm"
include "cfv.mm"
include "cle.mm"
include "wa.mm"
include "resubcld.mm"
include "eqidd.mm"
include "eqled.mm"
include "adantr.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "volico.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "wn.mm"
include "simpr.mm"
include "wb.mm"
include "lenltd.mm"
include "mpbird.mm"
include "suble0d.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem sublevolico
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  assume sublevolico.a: |- ( ph -> A e. RR )
  assume sublevolico.b: |- ( ph -> B e. RR )


  assert |- ( ph -> ( B - A ) <_ ( vol ` ( A [,) B ) ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    cmin
    co
    #
    cA
    cB
    cico
    co
    cvol
    cfv
    #
    cle
    wbr
    wph
    @0
    wa
    #
    @1
    @1
    @2
    cle
    wph
    @1
    @1
    cle
    wbr
    @0
    wph
    @1
    @1
    wph
    cB
    cA
    sublevolico.b
    sublevolico.a
    resubcld
    wph
    @1
    eqidd
    eqled
    adantr
    @3
    @2
    @0
    @1
    cc0
    cif
    #
    @1
    wph
    @2
    @4
    wceq
    #
    @0
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @5
    sublevolico.a
    sublevolico.b
    cA
    cB
    volico
    syl2anc
    #
    adantr
    @0
    @4
    @1
    wceq
    wph
    @0
    @1
    cc0
    iftrue
    adantl
    eqtr2d
    breqtrd
    wph
    @0
    wn
    #
    wa
    #
    @1
    cc0
    @2
    cle
    @10
    @1
    cc0
    cle
    wbr
    cB
    cA
    cle
    wbr
    #
    @10
    @11
    @9
    wph
    @9
    simpr
    wph
    @11
    @9
    wb
    @9
    wph
    cB
    cA
    sublevolico.b
    sublevolico.a
    lenltd
    adantr
    mpbird
    @10
    cB
    cA
    wph
    @7
    @9
    sublevolico.b
    adantr
    wph
    @6
    @9
    sublevolico.a
    adantr
    suble0d
    mpbird
    @10
    @2
    @4
    cc0
    wph
    @5
    @9
    @8
    adantr
    @9
    @4
    cc0
    wceq
    wph
    @0
    @1
    cc0
    iffalse
    adantl
    eqtr2d
    breqtrd
    pm2.61dan
end
